"""Huawei LUNA2000 helper for Predbat.

LIVE TOU TEST VERSION V6.3 - FUTURE-ONLY NATIVE TOU; EXPLICIT FALSE HANDOFF.

This laboratory version writes ONLY the Huawei TOU table and the three settings
needed to activate that table. It deliberately does NOT execute true-export
forcible_discharge commands. Predbat export windows are therefore left as gaps
in the TOU table so the real Huawei 'idle/no period' behaviour can be observed.

Control model previewed here:

* Base Huawei working mode: time_of_use_luna2000
* Predbat charge window: Huawei TOU "+"
* Normal battery/load support: Huawei TOU "-"
* Predbat hold / EV hold / freeze-charge: no TOU period
* Predbat true grid export: no TOU period in this test build. The timed
  huawei_solar.forcible_discharge command is previewed but NOT executed.
* Charge/export SOC targets remain diagnostic metadata only. Charge runs by
  complete 15-minute TOU slots; true export runs by a time-limited forcible
  discharge command that expires automatically at the end of the aligned slot.
* Predbat windows are expanded outwards to complete 15-minute Huawei control
  slots. The raw Predbat window is retained in the logs for comparison with
  Predbat's HTML plan.
* Export-freeze (99) remains a runtime-only concern because Huawei TOU has no
  exact equivalent for Predbat's export-freeze semantics.

The Huawei TOU service receives ONLY strings like:
    23:15-23:30/1234567/+

Home Assistant writes performed by this file are intentionally limited to:
    huawei_solar.set_tou_periods
    switch.batteries_charge_from_grid -> on
    select.batteries_excess_pv_energy_use_in_tou -> charge
    select.batteries_working_mode -> time_of_use_luna2000

The TOU table is staged first and must be confirmed by the readback sensor before
the working mode is enabled. True-export services are NOT called in this build.

apps.yaml master switch:
    huawei_tou: true   -> Predbat may own Huawei native TOU
    huawei_tou: false  -> if Huawei is currently in Predbat TOU mode, hand it back
                          to maximise_self_consumption and perform no further writes
"""

from datetime import timedelta
import time

from utils import calc_percent_limit


class HuaweiHelper:
    """Huawei LUNA2000 TOU live-test writer and diagnostics."""

    BUILD = "v6.3-future-only"

    TOU_SENSOR = "sensor.batteries_tou_charging_and_discharging_periods"
    WORKING_MODE_ENTITY = "select.batteries_working_mode"
    CHARGE_FROM_GRID_ENTITY = "switch.batteries_charge_from_grid"
    EXCESS_PV_ENTITY = "select.batteries_excess_pv_energy_use_in_tou"
    CAPACITY_CONTROL_ENTITY = "select.batteries_capacity_control_mode"

    WANTED_WORKING_MODE = "time_of_use_luna2000"
    FORCIBLE_DISCHARGE_SERVICE = "huawei_solar.forcible_discharge"
    STOP_FORCIBLE_SERVICE = "huawei_solar.stop_forcible_charge"
    WANTED_CHARGE_FROM_GRID = "on"
    WANTED_EXCESS_PV = "charge"

    TOU_DAYS = "1234567"
    TOU_HORIZON_MINUTES = 24 * 60
    TOU_MAX_PERIODS = 14
    CONTROL_SLOT_MINUTES = 15

    # LAB SWITCH: this V6 intentionally writes only the TOU control plane.
    TOU_WRITE_ENABLED = True
    TOU_WRITE_DEBOUNCE_SECONDS = 30
    FAILSAFE_WORKING_MODE = "maximise_self_consumption"
    SET_TOU_SERVICE = "huawei_solar/set_tou_periods"

    # Higher value wins if two Predbat intentions overlap on the absolute plan.
    PRIORITY = {
        "discharge": 0,
        "export_freeze": 5,
        "ev_hold": 20,
        "charge_hold": 30,
        "charge": 40,
        "export": 50,
    }

    def __init__(self, inverter):
        self.inverter = inverter
        self.base = inverter.base
        self.log = inverter.log

        self._last_preview_signature = None
        self._last_tou_conflicts = []
        self._last_export_freezes = []
        self._last_write_signature = None
        self._last_write_monotonic = None
        self._last_setting_requests = {}
        self._device_id_logged_missing = False
        self._last_control_enabled = None
        self.log("Huawei TOU CONTROL: loaded build {}".format(self.BUILD))

    # ---------------------------------------------------------------------
    # Generic helpers
    # ---------------------------------------------------------------------

    @staticmethod
    def _safe_float(value, default=None):
        try:
            return float(value)
        except (TypeError, ValueError):
            return default

    @staticmethod
    def _safe_int(value, default=None):
        try:
            return int(float(value))
        except (TypeError, ValueError):
            return default

    @staticmethod
    def _minute_to_hhmm(minute):
        """Convert clock minutes to HH:MM and preserve 24:00."""
        minute = int(minute)
        if minute == 1440:
            return "24:00"

        minute %= 1440
        return "{:02d}:{:02d}".format(minute // 60, minute % 60)

    def _absolute_label(self, minute):
        """Pretty-print Predbat absolute minutes."""
        try:
            dt = self.base.midnight_utc + timedelta(minutes=int(minute))
            return dt.strftime("%m-%d %H:%M")
        except Exception:
            return str(minute)

    @staticmethod
    def _state_key(state):
        """Stable hashable representation for one timeline state."""
        return (
            state.get("kind"),
            state.get("target_kwh"),
            state.get("target_percent"),
            state.get("reason"),
            state.get("source_start"),
            state.get("source_end"),
            state.get("car"),
        )

    @staticmethod
    def _same_state(first, second):
        return HuaweiHelper._state_key(first) == HuaweiHelper._state_key(second)

    def _clip_window(self, start, end, horizon_start, horizon_end):
        start = self._safe_int(start)
        end = self._safe_int(end)
        if start is None or end is None or end <= start:
            return None

        if end <= horizon_start or start >= horizon_end:
            return None

        return max(start, horizon_start), min(end, horizon_end)

    def _floor_to_control_slot(self, minute):
        minute = int(minute)
        step = self.CONTROL_SLOT_MINUTES
        return (minute // step) * step

    def _ceil_to_control_slot(self, minute):
        minute = int(minute)
        step = self.CONTROL_SLOT_MINUTES
        return ((minute + step - 1) // step) * step

    def _snap_window_outward(self, start, end):
        """Expand a Predbat window to complete 15-minute control slots.

        Example: 07:40-07:45 becomes 07:30-07:45. 08:40-09:00 becomes
        08:30-09:00. This deliberately preserves the whole market/control
        quarter containing a short Predbat action rather than dropping it.
        """
        start = self._safe_int(start)
        end = self._safe_int(end)
        if start is None or end is None or end <= start:
            return None
        return self._floor_to_control_slot(start), self._ceil_to_control_slot(end)

    def _format_absolute_window_clock(self, start, end):
        """Format an absolute Predbat window as clock HH:MM-HH:MM."""
        start = self._safe_int(start)
        end = self._safe_int(end)
        if start is None or end is None:
            return "?-?"

        start_clock = start % 1440
        end_clock = end % 1440
        # Preserve a midnight boundary as 24:00 when start/end are same day
        # or the end lands exactly on an absolute day boundary.
        if end > start and end_clock == 0:
            end_text = "24:00"
        else:
            end_text = self._minute_to_hhmm(end_clock)
        return "{}-{}".format(self._minute_to_hhmm(start_clock), end_text)

    def _new_state(
        self,
        kind,
        source_start=None,
        source_end=None,
        target_kwh=None,
        target_percent=None,
        reason=None,
        car=None,
    ):
        return {
            "kind": kind,
            "source_start": source_start,
            "source_end": source_end,
            "target_kwh": target_kwh,
            "target_percent": target_percent,
            "reason": reason,
            "car": car,
        }

    # ---------------------------------------------------------------------
    # Home Assistant readback
    # ---------------------------------------------------------------------

    def _get_state(self, entity_id):
        try:
            return self.base.get_state_wrapper(entity_id, default=None)
        except Exception as exc:
            self.log("Huawei TEST: Failed reading {}: {}".format(entity_id, exc))
            return None

    def read_huawei_state(self):
        """Read the Huawei configuration entities used by the future writer."""
        return {
            "working_mode": self._get_state(self.WORKING_MODE_ENTITY),
            "charge_from_grid": self._get_state(self.CHARGE_FROM_GRID_ENTITY),
            "excess_pv": self._get_state(self.EXCESS_PV_ENTITY),
            "capacity_control": self._get_state(self.CAPACITY_CONTROL_ENTITY),
        }

    def read_tou_periods(self):
        """Read the current Huawei TOU schedule from the diagnostic sensor.

        Returns:
            list[str]  - valid schedule, including [] for zero periods
            None       - sensor unavailable/invalid/incomplete
        """
        state = self._get_state(self.TOU_SENSOR)
        if state is None:
            return None

        state_text = str(state).strip().lower()
        if state_text in ("unknown", "unavailable", "none", ""):
            return None

        count = self._safe_int(state)
        if count is None or count < 0 or count > self.TOU_MAX_PERIODS:
            self.log(
                "Huawei TEST: Invalid TOU period count from {} = {}".format(
                    self.TOU_SENSOR, state
                )
            )
            return None

        if count == 0:
            return []

        periods = []
        for index in range(1, count + 1):
            attribute = "Period {}".format(index)
            try:
                value = self.base.get_state_wrapper(
                    self.TOU_SENSOR,
                    default=None,
                    attribute=attribute,
                )
            except Exception as exc:
                self.log(
                    "Huawei TEST: Failed reading {} attribute {}: {}".format(
                        self.TOU_SENSOR, attribute, exc
                    )
                )
                return None

            if value is None:
                self.log(
                    "Huawei TEST: TOU sensor says {} periods but {} is missing".format(
                        count, attribute
                    )
                )
                return None

            value = str(value).strip()
            if not value:
                return None
            periods.append(value)

        return periods

    # ---------------------------------------------------------------------
    # Predbat plan classification
    # ---------------------------------------------------------------------

    def _is_freeze_charge(self, charge_limit_kwh):
        try:
            if hasattr(self.base, "is_freeze_charge"):
                return bool(self.base.is_freeze_charge(charge_limit_kwh))
        except Exception:
            pass

        soc_max = self._safe_float(getattr(self.base, "soc_max", None), 0.0)
        reserve_percent = self._safe_float(
            getattr(self.base, "reserve_percent", None), None
        )
        if soc_max and reserve_percent is not None:
            return (
                calc_percent_limit(float(charge_limit_kwh), soc_max)
                == reserve_percent
            )
        return False

    def _charge_target_percent(self, charge_limit_kwh):
        soc_max = self._safe_float(getattr(self.base, "soc_max", None), 0.0)
        reserve = self._safe_float(getattr(self.base, "reserve", None), 0.0)
        if not soc_max:
            return None

        return float(
            calc_percent_limit(
                max(float(charge_limit_kwh), reserve or 0.0),
                soc_max,
            )
        )

    def _apply_state(
        self,
        timeline,
        horizon_start,
        horizon_end,
        start,
        end,
        state,
    ):
        """Overlay one intention onto the minute timeline."""
        clipped = self._clip_window(start, end, horizon_start, horizon_end)
        if not clipped:
            return

        clipped_start, clipped_end = clipped
        new_priority = self.PRIORITY[state["kind"]]

        for absolute_minute in range(clipped_start, clipped_end):
            index = absolute_minute - horizon_start
            old_state = timeline[index]
            old_priority = self.PRIORITY[old_state["kind"]]
            if new_priority >= old_priority:
                timeline[index] = state

    def _apply_charge_windows(self, timeline, horizon_start, horizon_end):
        windows = getattr(self.base, "charge_window_best", None) or []
        limits = getattr(self.base, "charge_limit_best", None) or []

        for index, window in enumerate(windows):
            if index >= len(limits):
                break

            limit = self._safe_float(limits[index])
            if limit is None:
                continue

            raw_start = self._safe_int(window.get("start"))
            raw_end = self._safe_int(window.get("end"))
            snapped = self._snap_window_outward(raw_start, raw_end)
            if not snapped:
                continue
            start, end = snapped

            target_percent = self._charge_target_percent(limit)

            if self._is_freeze_charge(limit):
                state = self._new_state(
                    "charge_hold",
                    source_start=raw_start,
                    source_end=raw_end,
                    target_kwh=limit,
                    target_percent=target_percent,
                    reason="Predbat freeze charge",
                )
            else:
                state = self._new_state(
                    "charge",
                    source_start=raw_start,
                    source_end=raw_end,
                    target_kwh=limit,
                    target_percent=target_percent,
                    reason="Predbat charge window",
                )

            self._apply_state(
                timeline,
                horizon_start,
                horizon_end,
                start,
                end,
                state,
            )

    def _apply_export_windows(self, timeline, horizon_start, horizon_end):
        windows = getattr(self.base, "export_window_best", None) or []
        limits = getattr(self.base, "export_limits_best", None) or []

        self._last_export_freezes = []
        self._last_write_signature = None
        self._last_write_monotonic = None
        self._last_setting_requests = {}
        self._device_id_logged_missing = False

        for index, window in enumerate(windows):
            if index >= len(limits):
                break

            limit = self._safe_float(limits[index])
            if limit is None:
                continue

            raw_start = self._safe_int(window.get("start"))
            raw_end = self._safe_int(window.get("end"))
            snapped = self._snap_window_outward(raw_start, raw_end)
            if not snapped:
                continue
            start, end = snapped

            # <99 is a real Predbat export. In the V5 model this is NOT a
            # Huawei TOU '-' period. The TOU list contains a gap for the slot
            # and runtime control uses a timed forcible_discharge command.
            if limit < 99.0:
                target = self._safe_float(window.get("target"), limit)
                state = self._new_state(
                    "export",
                    source_start=raw_start,
                    source_end=raw_end,
                    target_percent=target,
                    reason="Predbat true export -> timed forcible_discharge",
                )
                self._apply_state(
                    timeline,
                    horizon_start,
                    horizon_end,
                    start,
                    end,
                    state,
                )

            # 99 is Predbat export-freeze. Keep the base '-' schedule and log
            # the requirement separately until we have a faithful Huawei
            # mapping for this special Predbat state.
            elif limit == 99.0:
                clipped = self._clip_window(start, end, horizon_start, horizon_end)
                if clipped:
                    self._last_export_freezes.append(
                        {
                            "start": clipped[0],
                            "end": clipped[1],
                            "source_start": raw_start,
                            "source_end": raw_end,
                            "reason": "Predbat export freeze (runtime-only)",
                        }
                    )

    def _apply_ev_holds(self, timeline, horizon_start, horizon_end):
        if bool(getattr(self.base, "car_charging_from_battery", True)):
            return

        num_cars = self._safe_int(getattr(self.base, "num_cars", 0), 0) or 0
        slots_all = getattr(self.base, "car_charging_slots", None) or []
        soc_all = getattr(self.base, "car_charging_soc", None) or []
        limit_all = getattr(self.base, "car_charging_limit", None) or []

        for car_n in range(num_cars):
            if car_n >= len(slots_all):
                continue

            car_soc = (
                self._safe_float(soc_all[car_n], 0.0)
                if car_n < len(soc_all)
                else 0.0
            )
            car_limit = (
                self._safe_float(limit_all[car_n], 100.0)
                if car_n < len(limit_all)
                else 100.0
            )

            if car_soc is not None and car_limit is not None and car_soc >= car_limit:
                continue

            for window in slots_all[car_n] or []:
                raw_start = self._safe_int(window.get("start"))
                raw_end = self._safe_int(window.get("end"))
                kwh = self._safe_float(window.get("kwh"), 0.0) or 0.0
                snapped = self._snap_window_outward(raw_start, raw_end)
                if not snapped or kwh <= 0:
                    continue
                start, end = snapped

                state = self._new_state(
                    "ev_hold",
                    source_start=raw_start,
                    source_end=raw_end,
                    reason="EV hold - car_charging_from_battery is false",
                    car=car_n,
                )
                self._apply_state(
                    timeline,
                    horizon_start,
                    horizon_end,
                    start,
                    end,
                    state,
                )

    def _build_absolute_intervals(self):
        """Build the next 24 hours as a Predbat/Huawei control timeline."""
        horizon_start = int(self.base.minutes_now)
        horizon_end = horizon_start + self.TOU_HORIZON_MINUTES

        # Default TOU state is load support ("-"). Charge slots override
        # this with '+'. Hold/export slots deliberately create TOU gaps.
        timeline = [
            self._new_state(
                "discharge",
                reason="Normal load support",
            )
            for _ in range(self.TOU_HORIZON_MINUTES)
        ]

        # Overlay in increasing priority. _apply_state also protects priorities.
        self._apply_ev_holds(timeline, horizon_start, horizon_end)
        self._apply_charge_windows(timeline, horizon_start, horizon_end)
        self._apply_export_windows(timeline, horizon_start, horizon_end)

        intervals = []
        interval_start = horizon_start
        current_state = timeline[0]

        for offset in range(1, len(timeline)):
            state = timeline[offset]
            if not self._same_state(state, current_state):
                intervals.append(
                    {
                        "absolute_start": interval_start,
                        "absolute_end": horizon_start + offset,
                        "state": current_state,
                    }
                )
                interval_start = horizon_start + offset
                current_state = state

        intervals.append(
            {
                "absolute_start": interval_start,
                "absolute_end": horizon_end,
                "state": current_state,
            }
        )

        # If the currently active special window started before "now", preserve
        # its original start. This stops a persistent TOU period moving forward
        # one minute at every Predbat run. Later occurrences of the same clock
        # minutes are intentionally deferred by the clock compiler below.
        if intervals:
            first = intervals[0]
            state = first["state"]
            source_start = self._safe_int(state.get("source_start"))
            source_end = self._safe_int(state.get("source_end"))
            snapped = self._snap_window_outward(source_start, source_end)
            if state.get("kind") != "discharge" and snapped:
                snapped_start, snapped_end = snapped
                if snapped_start < horizon_start < snapped_end:
                    first["absolute_start"] = snapped_start

        return horizon_start, horizon_end, intervals

    # ---------------------------------------------------------------------
    # Absolute 24h -> recurring Huawei clock plan
    # ---------------------------------------------------------------------

    def _split_interval_at_midnight(self, interval):
        """Split an absolute interval into one or more clock-day segments."""
        start = int(interval["absolute_start"])
        end = int(interval["absolute_end"])
        state = interval["state"]

        result = []
        cursor = start

        while cursor < end:
            day_index = cursor // 1440
            day_end = (day_index + 1) * 1440
            segment_end = min(end, day_end)

            start_minute = cursor - day_index * 1440
            end_minute = segment_end - day_index * 1440

            # Midnight at the end of a day is represented as 24:00.
            if segment_end == day_end:
                end_minute = 1440

            result.append(
                {
                    "absolute_start": cursor,
                    "absolute_end": segment_end,
                    "day_index": day_index,
                    "start_minute": start_minute,
                    "end_minute": end_minute,
                    "state": state,
                }
            )
            cursor = segment_end

        return result

    def _compile_clock_intervals(self, absolute_intervals):
        """Compile the rolling 24h plan into one recurring 00:00-24:00 day.

        Because every Huawei period uses /1234567/, two different absolute days
        cannot carry different commands for the same clock minute. The nearest
        chronological occurrence wins. Later conflicting intent is logged as
        deferred and will be picked up by a later Predbat re-plan.
        """
        segments = []
        for interval in absolute_intervals:
            segments.extend(self._split_interval_at_midnight(interval))

        segments.sort(key=lambda item: item["absolute_start"])

        clock_state = [None] * 1440
        clock_source = [None] * 1440
        conflicts = []

        for segment in segments:
            start_minute = int(segment["start_minute"])
            end_minute = int(segment["end_minute"])
            state = segment["state"]

            for clock_minute in range(start_minute, end_minute):
                if clock_state[clock_minute] is None:
                    clock_state[clock_minute] = state
                    clock_source[clock_minute] = segment
                elif not self._same_state(clock_state[clock_minute], state):
                    conflicts.append(
                        {
                            "clock_minute": clock_minute,
                            "kept": clock_source[clock_minute],
                            "deferred": segment,
                        }
                    )

        # The 24h source timeline should fill the whole recurring day. If it
        # does not, leave those minutes as explicit hold/idle rather than invent
        # a discharge command.
        idle_state = self._new_state(
            "ev_hold",
            reason="Compiler gap - fail safe idle",
        )
        for minute in range(1440):
            if clock_state[minute] is None:
                clock_state[minute] = idle_state

        # Deduplicate conflicts into contiguous ranges with the same kept/defer
        # state to keep logs readable.
        compact_conflicts = []
        for conflict in conflicts:
            key = (
                self._state_key(conflict["kept"]["state"]),
                self._state_key(conflict["deferred"]["state"]),
            )
            if (
                compact_conflicts
                and compact_conflicts[-1]["end"] == conflict["clock_minute"]
                and compact_conflicts[-1]["key"] == key
            ):
                compact_conflicts[-1]["end"] += 1
            else:
                compact_conflicts.append(
                    {
                        "start": conflict["clock_minute"],
                        "end": conflict["clock_minute"] + 1,
                        "key": key,
                        "kept": conflict["kept"],
                        "deferred": conflict["deferred"],
                    }
                )

        self._last_tou_conflicts = compact_conflicts

        # Compress the final recurring clock day.
        intervals = []
        start = 0
        current = clock_state[0]

        for minute in range(1, 1440):
            if not self._same_state(clock_state[minute], current):
                intervals.append(
                    {
                        "start_minute": start,
                        "end_minute": minute,
                        "state": current,
                    }
                )
                start = minute
                current = clock_state[minute]

        intervals.append(
            {
                "start_minute": start,
                "end_minute": 1440,
                "state": current,
            }
        )

        return intervals

    # ---------------------------------------------------------------------
    # Public preview builders
    # ---------------------------------------------------------------------

    def build_control_preview(self):
        """Return the complete read-only Huawei V5 control preview."""
        horizon_start, horizon_end, absolute_intervals = self._build_absolute_intervals()
        clock_intervals = self._compile_clock_intervals(absolute_intervals)

        periods = []
        actions = []

        for interval in clock_intervals:
            start_minute = interval["start_minute"]
            end_minute = interval["end_minute"]
            state = interval["state"]
            kind = state["kind"]

            item = {
                "start_minute": start_minute,
                "end_minute": end_minute,
                "start": self._minute_to_hhmm(start_minute),
                "end": self._minute_to_hhmm(end_minute),
                "days": self.TOU_DAYS,
                "kind": kind,
                "target_kwh": state.get("target_kwh"),
                "target_percent": state.get("target_percent"),
                "reason": state.get("reason"),
                "car": state.get("car"),
                "source_start": state.get("source_start"),
                "source_end": state.get("source_end"),
            }

            if kind == "charge":
                # Native Huawei TOU charging. Predbat target SOC is diagnostic
                # only; the complete 15-minute slot is allowed to run.
                item["flag"] = "+"
                periods.append(item)
                actions.append(
                    {
                        **item,
                        "runtime_action": "tou_charge_plus",
                    }
                )
            elif kind == "discharge":
                item["flag"] = "-"
                periods.append(item)
            elif kind == "export":
                # No TOU period during true export. Runtime control uses the
                # Huawei timed forcible_discharge service. The command is
                # bounded by duration, so Huawei automatically stops at the
                # end of the aligned export interval even if Predbat stops.
                aligned = self._snap_window_outward(
                    state.get("source_start"), state.get("source_end")
                )
                duration_minutes = (
                    max(1, aligned[1] - aligned[0]) if aligned else max(1, end_minute - start_minute)
                )
                actions.append(
                    {
                        **item,
                        "runtime_action": "forcible_discharge_time",
                        "service": self.FORCIBLE_DISCHARGE_SERVICE,
                        "power_w": self.get_export_power_w(),
                        "duration_minutes": duration_minutes,
                        "aligned_absolute_start": aligned[0] if aligned else None,
                        "aligned_absolute_end": aligned[1] if aligned else None,
                    }
                )
            elif kind in ("ev_hold", "charge_hold"):
                actions.append(
                    {
                        **item,
                        "runtime_action": "hold_no_tou_period",
                    }
                )

        # The rolling 24h clock preview above is useful diagnostically, but the
        # live Huawei table must not waste slots on clock periods that already
        # elapsed today. Rebuild the writable table directly from the absolute
        # timeline, retaining only the current slot and the remainder of today.
        # Midnight is always a hard split; tomorrow is written after midnight.
        periods = self._build_future_current_day_tou_periods(
            absolute_intervals, horizon_start
        )

        # Adjacent true-export quarters are one continuous timed override.
        # Merge them so e.g. 08:00-08:15 + 08:15-08:30 + 08:30-09:30
        # becomes a single 08:00-09:30 forcible_discharge preview.
        actions = self._merge_adjacent_export_actions(actions)

        for freeze in self._last_export_freezes:
            actions.append(
                {
                    "kind": "export_freeze",
                    "absolute_start": freeze["start"],
                    "absolute_end": freeze["end"],
                    "source_start": freeze.get("source_start"),
                    "source_end": freeze.get("source_end"),
                    "reason": freeze["reason"],
                    "runtime_action": "runtime_export_freeze",
                }
            )

        return {
            "horizon_start": horizon_start,
            "horizon_end": horizon_end,
            "absolute_intervals": absolute_intervals,
            "clock_intervals": clock_intervals,
            "periods": periods,
            "actions": actions,
            "conflicts": list(self._last_tou_conflicts),
        }

    def _build_future_current_day_tou_periods(self, absolute_intervals, horizon_start):
        """Build only the TOU periods that are still relevant today.

        Huawei TOU periods are recurring clock entries. Keeping periods whose
        end time has already passed wastes one of the 14 hardware slots and can
        make a busy Predbat plan fail validation. For the live table we therefore
        keep only the current control slot and future intervals up to 24:00.

        Midnight is a hard boundary: nothing is carried through 24:00 in one
        period. The next Predbat run after midnight writes a new 00:00-based
        table for the new day. Until then, the omitted early-day clock range is
        simply a TOU gap (fail-safe idle rather than a stale command).
        """
        now_abs = int(horizon_start)
        day_base = (now_abs // 1440) * 1440
        day_end = day_base + 1440

        # Retain the currently active 15-minute control quantum rather than
        # starting a rewritten TOU period at an arbitrary minute such as 18:25.
        slot_start_abs = day_base + ((now_abs - day_base) // self.CONTROL_SLOT_MINUTES) * self.CONTROL_SLOT_MINUTES

        periods = []
        for interval in absolute_intervals:
            interval_start = int(interval["absolute_start"])
            interval_end = int(interval["absolute_end"])

            # Fully expired, or entirely on the next day.
            if interval_end <= now_abs or interval_start >= day_end:
                continue

            state = interval["state"]
            kind = state.get("kind")
            if kind not in ("charge", "discharge"):
                # Hold/export remain real TOU gaps.
                continue

            start_abs = max(interval_start, slot_start_abs)
            end_abs = min(interval_end, day_end)
            if start_abs >= end_abs:
                continue

            start_minute = start_abs - day_base
            end_minute = end_abs - day_base

            # A segment that reaches midnight ends at Huawei's valid 24:00.
            # It is never merged with a 00:00 segment from the next day.
            item = {
                "start_minute": start_minute,
                "end_minute": end_minute,
                "start": self._minute_to_hhmm(start_minute),
                "end": self._minute_to_hhmm(end_minute),
                "days": self.TOU_DAYS,
                "kind": kind,
                "flag": "+" if kind == "charge" else "-",
                "target_kwh": state.get("target_kwh"),
                "target_percent": state.get("target_percent"),
                "reason": state.get("reason"),
                "car": state.get("car"),
                "source_start": state.get("source_start"),
                "source_end": state.get("source_end"),
            }
            periods.append(item)

        return self._merge_adjacent_tou_periods(periods)

    def get_export_power_w(self):
        """Return Predbat's configured maximum discharge power in watts.

        Predbat stores battery_rate_max_discharge as kWh per minute. The
        MINUTE_WATT conversion used by Predbat is 60 * 1000. Keep this helper
        local so huawei.py does not need another import solely for one constant.
        """
        rate = self._safe_float(
            getattr(self.inverter, "battery_rate_max_discharge", None)
        )
        if rate is None:
            rate = self._safe_float(
                getattr(self.base, "battery_rate_max_discharge", None)
            )
        if rate is None or rate <= 0:
            return None
        return max(1, int(round(rate * 60 * 1000)))

    def _merge_adjacent_export_actions(self, actions):
        """Merge touching export actions into one timed discharge command."""
        if not actions:
            return []

        merged = []
        for action in actions:
            if action.get("kind") != "export":
                merged.append(dict(action))
                continue

            current = dict(action)
            if (
                merged
                and merged[-1].get("kind") == "export"
                and merged[-1].get("end_minute") == current.get("start_minute")
            ):
                previous = merged[-1]
                previous["end_minute"] = current.get("end_minute")
                previous["end"] = current.get("end")
                previous["duration_minutes"] = max(
                    1,
                    int(previous["end_minute"]) - int(previous["start_minute"]),
                )
                if current.get("aligned_absolute_end") is not None:
                    previous["aligned_absolute_end"] = current.get("aligned_absolute_end")
                # Targets are diagnostic only. Keep the last one because it
                # best describes Predbat's end-state expectation.
                previous["target_kwh"] = current.get("target_kwh")
                previous["target_percent"] = current.get("target_percent")
                previous["source_end"] = current.get("source_end")
                continue

            merged.append(current)

        return merged

    def active_export_command(self, preview=None):
        """Return the active timed export command, including remaining minutes.

        This is read-only. It uses the absolute 24-hour timeline rather than
        the recurring clock plan, so a restart in the middle of an export
        window produces only the time remaining until the real window end.
        """
        if preview is None:
            preview = self.build_control_preview()

        now = int(self.base.minutes_now)
        intervals = preview.get("absolute_intervals") or []
        for index, interval in enumerate(intervals):
            if interval["state"].get("kind") != "export":
                continue
            start = int(interval["absolute_start"])
            end = int(interval["absolute_end"])
            if start <= now < end:
                # Predbat can express one continuous 15-minute export run as
                # several raw best-window fragments. Extend across directly
                # touching export intervals so one timed Huawei command can
                # cover the complete continuous run.
                for following in intervals[index + 1 :]:
                    if following["state"].get("kind") != "export":
                        break
                    following_start = int(following["absolute_start"])
                    if following_start != end:
                        break
                    end = int(following["absolute_end"])

                return {
                    "service": self.FORCIBLE_DISCHARGE_SERVICE,
                    "power_w": self.get_export_power_w(),
                    "duration_minutes": max(1, end - now),
                    "absolute_start": start,
                    "absolute_end": end,
                    "target_percent": interval["state"].get("target_percent"),
                    "source_start": interval["state"].get("source_start"),
                    "source_end": interval["state"].get("source_end"),
                }
        return None

    def _merge_adjacent_tou_periods(self, periods):
        """Merge touching Huawei periods with the same +/- command.

        Predbat may expose several adjacent windows with different target SOC
        metadata. Huawei TOU does not carry that metadata, so those windows are
        one hardware command and should consume only one of Huawei's 14 slots.
        """
        if not periods:
            return []

        merged = []
        for period in sorted(periods, key=lambda item: item["start_minute"]):
            if (
                merged
                and merged[-1]["flag"] == period["flag"]
                and merged[-1]["end_minute"] == period["start_minute"]
            ):
                merged[-1]["end_minute"] = period["end_minute"]
                merged[-1]["end"] = period["end"]
            else:
                merged.append(dict(period))
        return merged

    @staticmethod
    def _period_to_text(period):
        """Serialize ONLY fields accepted by huawei_solar.set_tou_periods."""
        return "{}-{}/{}/{}".format(
            period["start"],
            period["end"],
            period["days"],
            period["flag"],
        )

    def tou_preview_as_text(self, periods=None):
        if periods is None:
            periods = self.build_control_preview()["periods"]
        return [self._period_to_text(period) for period in periods]

    def validate_tou_preview(self, periods):
        errors = []

        if len(periods) > self.TOU_MAX_PERIODS:
            errors.append(
                "too many periods: {} > {}".format(
                    len(periods), self.TOU_MAX_PERIODS
                )
            )

        occupied = [None] * 1440

        for index, period in enumerate(periods, start=1):
            start = self._safe_int(period.get("start_minute"))
            end = self._safe_int(period.get("end_minute"))
            days = period.get("days")
            flag = period.get("flag")

            if start is None or end is None:
                errors.append("period {} has invalid time".format(index))
                continue

            if not (0 <= start < end <= 1440):
                errors.append(
                    "period {} has invalid range {}-{}".format(index, start, end)
                )
                continue

            if days != self.TOU_DAYS:
                errors.append(
                    "period {} days are {} not {}".format(
                        index, days, self.TOU_DAYS
                    )
                )

            if flag not in ("+", "-"):
                errors.append("period {} has invalid flag {}".format(index, flag))

            for minute in range(start, end):
                if occupied[minute] is not None:
                    errors.append(
                        "period {} overlaps period {} at {}".format(
                            index,
                            occupied[minute],
                            self._minute_to_hhmm(minute),
                        )
                    )
                    break
                occupied[minute] = index

        return errors

    # ---------------------------------------------------------------------
    # LIVE TOU TEST WRITER
    # ---------------------------------------------------------------------

    @staticmethod
    def _normalize_period_strings(periods):
        return sorted(str(item).strip() for item in (periods or []))

    def _get_raw_arg_for_inverter(self, name):
        """Read one raw Predbat/AppDaemon argument without entity resolution."""
        try:
            value = self.base.args.get(name)
        except Exception:
            return None

        if isinstance(value, list):
            if not value:
                return None
            index = self._safe_int(getattr(self.inverter, "id", 0), 0) or 0
            if 0 <= index < len(value):
                value = value[index]
            else:
                value = value[0]
        return value

    def resolve_huawei_device_id(self):
        """Resolve the HA Huawei battery device_id without hard-coding it.

        Prefer an explicit huawei_device_id/predbat_huawei_device_id argument.
        If that is not present, reuse the already-resolved device_id from the
        user's existing Huawei charge/discharge service template.
        """
        for name in ("huawei_device_id", "predbat_huawei_device_id"):
            value = self._get_raw_arg_for_inverter(name)
            if isinstance(value, str) and value.strip():
                return value.strip()

        for name in (
            "charge_start_service",
            "charge_stop_service",
            "discharge_start_service",
            "discharge_stop_service",
        ):
            value = self._get_raw_arg_for_inverter(name)
            if not isinstance(value, dict):
                continue
            device_id = value.get("device_id")
            if isinstance(device_id, str) and device_id.strip():
                return device_id.strip()

            data = value.get("data")
            if isinstance(data, dict):
                device_id = data.get("device_id")
                if isinstance(device_id, str) and device_id.strip():
                    return device_id.strip()
        return None

    def huawei_tou_enabled(self):
        """Return the apps.yaml Huawei master switch.

        This is deliberately a plain apps.yaml boolean, not a Home Assistant
        switch/entity. Default is False so an omitted setting cannot take
        ownership of the inverter by accident.
        """
        try:
            value = self.base.get_arg("huawei_tou", False, indirect=False)
        except TypeError:
            # Compatibility with older get_arg signatures.
            value = self.base.get_arg("huawei_tou", False)

        if isinstance(value, str):
            return value.strip().lower() in ("1", "true", "yes", "on", "enable", "enabled")
        return bool(value)

    def _handoff_to_self_consumption(self, reason):
        """Leave native Huawei TOU when Predbat Huawei control is disabled.

        Only write when Huawei is actually in the working mode owned by this
        helper. Once maximise_self_consumption is confirmed, no more writes are
        made while huawei_tou remains False. The stored TOU table is left intact
        but inactive.
        """
        current_mode = self._get_state(self.WORKING_MODE_ENTITY)

        if current_mode == self.FAILSAFE_WORKING_MODE:
            self._last_setting_requests.pop("handoff_mode", None)
            return True

        # Do not take control away from some other controller/mode. We only
        # hand off a TOU mode that this helper itself uses.
        if current_mode != self.WANTED_WORKING_MODE:
            return True

        if not self._service_request_allowed(
            "handoff_mode", self.FAILSAFE_WORKING_MODE
        ):
            return False

        self.log(
            "Huawei TOU CONTROL: HANDOFF {} -> {} because {}".format(
                self.WORKING_MODE_ENTITY, self.FAILSAFE_WORKING_MODE, reason
            )
        )
        self.base.call_service_wrapper(
            "select/select_option",
            entity_id=self.WORKING_MODE_ENTITY,
            option=self.FAILSAFE_WORKING_MODE,
        )
        return False

    def _service_request_allowed(self, key, value):
        """Suppress duplicate writes while HA/Huawei readback catches up."""
        now = time.monotonic()
        previous = self._last_setting_requests.get(key)
        if previous:
            previous_value, previous_time = previous
            if previous_value == value and (now - previous_time) < self.TOU_WRITE_DEBOUNCE_SECONDS:
                return False
        self._last_setting_requests[key] = (value, now)
        return True

    def _set_select(self, entity_id, option):
        current = self._get_state(entity_id)
        if current == option:
            self._last_setting_requests.pop(entity_id, None)
            return True
        if not self._service_request_allowed(entity_id, option):
            return False
        self.log("Huawei TOU WRITE TEST: select {} -> {}".format(entity_id, option))
        self.base.call_service_wrapper(
            "select/select_option",
            entity_id=entity_id,
            option=option,
        )
        return False

    def _set_switch_on(self, entity_id):
        current = self._get_state(entity_id)
        if str(current).lower() == "on":
            self._last_setting_requests.pop(entity_id, None)
            return True
        if not self._service_request_allowed(entity_id, "on"):
            return False
        self.log("Huawei TOU WRITE TEST: switch {} -> on".format(entity_id))
        self.base.call_service_wrapper("switch/turn_on", entity_id=entity_id)
        return False

    def _failsafe_leave_tou(self, reason):
        """If the test plan is unusable, do not leave a stale TOU active."""
        current_mode = self._get_state(self.WORKING_MODE_ENTITY)
        if current_mode != self.WANTED_WORKING_MODE:
            return
        if not self._service_request_allowed(
            "failsafe_mode", self.FAILSAFE_WORKING_MODE
        ):
            return
        self.log(
            "Huawei TOU WRITE TEST: FAILSAFE {} -> {} because {}".format(
                self.WORKING_MODE_ENTITY, self.FAILSAFE_WORKING_MODE, reason
            )
        )
        self.base.call_service_wrapper(
            "select/select_option",
            entity_id=self.WORKING_MODE_ENTITY,
            option=self.FAILSAFE_WORKING_MODE,
        )

    def write_tou_test(self, preview=None, current=None, huawei_state=None):
        """Stage the sparse TOU table and enable TOU only after readback matches.

        IMPORTANT: This function never calls forcible_discharge. Export/hold
        intervals are intentionally represented by gaps between TOU periods.
        That is the behaviour this laboratory build is meant to test.
        """
        enabled = self.huawei_tou_enabled()
        if not enabled:
            self._handoff_to_self_consumption("huawei_tou=false")
            return False

        if not self.TOU_WRITE_ENABLED:
            return False

        if preview is None:
            preview = self.build_control_preview()
        periods = preview.get("periods") or []
        errors = self.validate_tou_preview(periods)
        wanted = self.tou_preview_as_text(periods)

        if errors:
            self.log(
                "Huawei TOU WRITE TEST: REFUSED - invalid generated schedule: {}".format(
                    "; ".join(errors)
                )
            )
            self._failsafe_leave_tou("generated TOU validation failed")
            return False

        # Sparse schedules are valid and are exactly how we test IDLE: gaps
        # between periods are left completely absent. An entirely empty table
        # is a separate edge case. huawei_solar's current service regex accepts
        # an empty string, but its parser then tries to parse that empty line.
        # Do not invent a dummy period automatically until hardware behaviour
        # has been verified.
        if not wanted:
            self.log(
                "Huawei TOU WRITE TEST: REFUSED - generated table has zero periods; "
                "not sending empty string and not inventing a dummy period"
            )
            self._failsafe_leave_tou("zero-period TOU table not yet hardware-tested")
            return False

        device_id = self.resolve_huawei_device_id()
        if not device_id:
            if not self._device_id_logged_missing:
                self.log(
                    "Huawei TOU WRITE TEST: REFUSED - Huawei device_id not found. "
                    "Add huawei_device_id: !secret predbat_huawei_device_id, or keep "
                    "device_id in the existing Huawei charge/discharge service template."
                )
                self._device_id_logged_missing = True
            return False
        self._device_id_logged_missing = False

        if current is None:
            current = self.read_tou_periods()
        if current is None:
            self.log(
                "Huawei TOU WRITE TEST: REFUSED - current TOU readback unavailable; "
                "will not activate/write blind"
            )
            return False

        wanted_norm = self._normalize_period_strings(wanted)
        current_norm = self._normalize_period_strings(current)

        if current_norm != wanted_norm:
            signature = tuple(wanted)
            now = time.monotonic()
            if (
                self._last_write_signature == signature
                and self._last_write_monotonic is not None
                and (now - self._last_write_monotonic) < self.TOU_WRITE_DEBOUNCE_SECONDS
            ):
                self.log(
                    "Huawei TOU WRITE TEST: waiting for TOU readback after previous write"
                )
                return False

            periods_text = "\n".join(wanted)
            self.log(
                "Huawei TOU WRITE TEST: writing {} TOU period(s); gaps remain IDLE/no-period".format(
                    len(wanted)
                )
            )
            for index, line in enumerate(wanted, start=1):
                self.log("Huawei TOU WRITE TEST: WRITE {} = {}".format(index, line))

            self.base.call_service_wrapper(
                self.SET_TOU_SERVICE,
                device_id=device_id,
                periods=periods_text,
            )
            self._last_write_signature = signature
            self._last_write_monotonic = now
            return False

        # Sensor truth wins once the table matches. Clear pending-write state.
        self._last_write_signature = None
        self._last_write_monotonic = None

        if huawei_state is None:
            huawei_state = self.read_huawei_state()

        # Configure settings used by native TOU. Do this before activating TOU.
        grid_ok = str(huawei_state.get("charge_from_grid")).lower() == "on"
        if not grid_ok:
            self._set_switch_on(self.CHARGE_FROM_GRID_ENTITY)
            return False

        excess_ok = huawei_state.get("excess_pv") == self.WANTED_EXCESS_PV
        if not excess_ok:
            self._set_select(self.EXCESS_PV_ENTITY, self.WANTED_EXCESS_PV)
            return False

        mode_ok = huawei_state.get("working_mode") == self.WANTED_WORKING_MODE
        if not mode_ok:
            self._set_select(self.WORKING_MODE_ENTITY, self.WANTED_WORKING_MODE)
            return False

        self._last_setting_requests.clear()
        self.log(
            "Huawei TOU WRITE TEST: ACTIVE - table readback matches and working mode is {}".format(
                self.WANTED_WORKING_MODE
            )
        )
        return True

    # ---------------------------------------------------------------------
    # Logging
    # ---------------------------------------------------------------------

    def log_tou_periods(self):
        periods = self.read_tou_periods()
        if periods is None:
            self.log("Huawei TEST: Current TOU schedule unavailable")
            return

        self.log(
            "Huawei TEST: Current TOU schedule contains {} period(s)".format(
                len(periods)
            )
        )
        for index, period in enumerate(periods, start=1):
            self.log("Huawei TEST: Period {} = {}".format(index, period))

    def _format_target(self, item):
        target_kwh = item.get("target_kwh")
        target_percent = item.get("target_percent")

        parts = []
        if target_kwh is not None:
            parts.append("{:.2f} kWh".format(float(target_kwh)))
        if target_percent is not None:
            parts.append("{}%".format(round(float(target_percent), 1)))

        return " / ".join(parts) if parts else "-"

    def log_huawei_state_preview(self, huawei_state=None):
        if huawei_state is None:
            huawei_state = self.read_huawei_state()

        self.log("Huawei STATE TEST: =======================================")
        self.log(
            "Huawei STATE TEST: Working mode       = {}".format(
                huawei_state["working_mode"]
            )
        )
        self.log(
            "Huawei STATE TEST: Wanted             = {}".format(
                self.WANTED_WORKING_MODE
            )
        )
        self.log(
            "Huawei STATE TEST: Working mode OK    = {}".format(
                huawei_state["working_mode"] == self.WANTED_WORKING_MODE
            )
        )
        self.log(
            "Huawei STATE TEST: True export service = {} (timed runtime override)".format(
                self.FORCIBLE_DISCHARGE_SERVICE
            )
        )

        self.log(
            "Huawei STATE TEST: Charge from grid   = {}".format(
                huawei_state["charge_from_grid"]
            )
        )
        self.log(
            "Huawei STATE TEST: Wanted             = {}".format(
                self.WANTED_CHARGE_FROM_GRID
            )
        )
        self.log(
            "Huawei STATE TEST: Charge from grid OK= {}".format(
                huawei_state["charge_from_grid"] == self.WANTED_CHARGE_FROM_GRID
            )
        )

        self.log(
            "Huawei STATE TEST: Excess PV          = {}".format(
                huawei_state["excess_pv"]
            )
        )
        self.log(
            "Huawei STATE TEST: Wanted             = {}".format(
                self.WANTED_EXCESS_PV
            )
        )
        self.log(
            "Huawei STATE TEST: Excess PV OK       = {}".format(
                huawei_state["excess_pv"] == self.WANTED_EXCESS_PV
            )
        )
        self.log(
            "Huawei STATE TEST: Capacity control   = {} (ignored)".format(
                huawei_state["capacity_control"]
            )
        )
        self.log("Huawei STATE TEST: =======================================")

    def log_tou_preview(self, preview=None):
        if preview is None:
            preview = self.build_control_preview()

        periods = preview["periods"]
        errors = self.validate_tou_preview(periods)

        self.log("Huawei TOU PREVIEW: ========================================")
        self.log(
            "Huawei TOU PREVIEW: Rolling source horizon {} -> {} (24 hours)".format(
                self._absolute_label(preview["horizon_start"]),
                self._absolute_label(preview["horizon_end"]),
            )
        )
        self.log(
            "Huawei TOU PREVIEW: Writable future-of-today table has {} period(s)".format(
                len(periods)
            )
        )
        self.log(
            "Huawei TOU PREVIEW: Validation = {}".format(
                "OK" if not errors else "ERROR"
            )
        )

        for error in errors:
            self.log("Huawei TOU PREVIEW: ERROR: {}".format(error))

        for index, period in enumerate(periods, start=1):
            self.log(
                "Huawei TOU PREVIEW: Period {} = {}".format(
                    index, self._period_to_text(period)
                )
            )

        for conflict in preview["conflicts"]:
            kept_state = conflict["kept"]["state"]
            deferred_state = conflict["deferred"]["state"]
            self.log(
                "Huawei TOU PREVIEW: KEEP {}-{} {} / DEFER later {}".format(
                    self._minute_to_hhmm(conflict["start"]),
                    self._minute_to_hhmm(conflict["end"]),
                    kept_state.get("kind"),
                    deferred_state.get("kind"),
                )
            )

        self.log("Huawei TOU PREVIEW: ========================================")

    def log_action_preview(self, preview=None):
        if preview is None:
            preview = self.build_control_preview()

        self.log("Huawei ACTION PREVIEW: =====================================")
        self.log(
            "Huawei ACTION PREVIEW: Control quantum = {} minutes".format(
                self.CONTROL_SLOT_MINUTES
            )
        )

        for action in preview["actions"]:
            kind = action.get("kind")
            runtime_action = action.get("runtime_action")

            if kind == "export_freeze":
                raw = self._format_absolute_window_clock(
                    action.get("source_start"), action.get("source_end")
                )
                effective = "{}-{}".format(
                    self._absolute_label(action["absolute_start"]),
                    self._absolute_label(action["absolute_end"]),
                )
                self.log(
                    "Huawei ACTION PREVIEW: EXPORT FREEZE raw {} -> aligned {} "
                    "-> {} ({})".format(
                        raw, effective, runtime_action, action.get("reason")
                    )
                )
                continue

            clock = "{}-{}".format(action.get("start"), action.get("end"))
            raw = self._format_absolute_window_clock(
                action.get("source_start"), action.get("source_end")
            )
            alignment = "raw {} -> slot {}".format(raw, clock)

            if kind == "charge":
                self.log(
                    "Huawei ACTION PREVIEW: CHARGE {} target {} -> TOU + "
                    "(target informational; full slot runs)".format(
                        alignment, self._format_target(action)
                    )
                )
            elif kind == "export":
                self.log(
                    "Huawei ACTION PREVIEW: EXPORT {} target {} -> NO TOU "
                    "period; {} power={}W duration={}m; auto-stop -> TOU".format(
                        alignment,
                        self._format_target(action),
                        action.get("service"),
                        action.get("power_w"),
                        action.get("duration_minutes"),
                    )
                )
            elif kind == "ev_hold":
                self.log(
                    "Huawei ACTION PREVIEW: EV HOLD {} car {} -> NO TOU "
                    "period; PV charging remains allowed".format(
                        alignment, action.get("car")
                    )
                )
            elif kind == "charge_hold":
                self.log(
                    "Huawei ACTION PREVIEW: CHARGE HOLD {} target {} -> NO "
                    "TOU period".format(
                        alignment, self._format_target(action)
                    )
                )

        if (
            bool(getattr(self.base, "iboost_enable", False))
            and bool(getattr(self.base, "iboost_prevent_discharge", False))
            and bool(getattr(self.base, "iboost_running_full", False))
        ):
            self.log(
                "Huawei ACTION PREVIEW: iBoost runtime hold is ACTIVE; "
                "future end time is not available in this compiler, so it "
                "remains runtime-only for now"
            )

        active = self.active_export_command(preview)
        if active:
            self.log(
                "Huawei ACTION PREVIEW: ACTIVE EXPORT NOW -> {} power={}W "
                "remaining={}m until {}; if restarted now use remaining time only".format(
                    active["service"],
                    active.get("power_w"),
                    active["duration_minutes"],
                    self._absolute_label(active["absolute_end"]),
                )
            )

        self.log("Huawei ACTION PREVIEW: =====================================")

    def log_tou_compare(self, preview=None, current=None):
        if preview is None:
            preview = self.build_control_preview()
        if current is None:
            current = self.read_tou_periods()

        wanted = self.tou_preview_as_text(preview["periods"])

        self.log("Huawei TOU COMPARE: ========================================")

        if current is None:
            self.log("Huawei TOU COMPARE: Current schedule unavailable")
            self.log("Huawei TOU COMPARE: Would NOT write while readback is invalid")
            self.log("Huawei TOU COMPARE: ========================================")
            return

        for index, period in enumerate(current, start=1):
            self.log("Huawei TOU COMPARE: Current {} = {}".format(index, period))
        for index, period in enumerate(wanted, start=1):
            self.log("Huawei TOU COMPARE: Wanted  {} = {}".format(index, period))

        current_normalized = sorted(str(item).strip() for item in current)
        wanted_normalized = sorted(str(item).strip() for item in wanted)

        self.log(
            "Huawei TOU COMPARE: Schedule changed = {}".format(
                current_normalized != wanted_normalized
            )
        )
        self.log("Huawei TOU COMPARE: ========================================")

    def log_predbat_plan_preview(self):
        """Main entry point called from execute.py.

        V6.3 writes only the still-relevant part of today's sparse TOU table and activates native Huawei TOU only
        after exact sensor readback. Timed true-export commands remain preview-only.
        """
        enabled = self.huawei_tou_enabled()
        if enabled != self._last_control_enabled:
            self.log(
                "Huawei TOU CONTROL: huawei_tou={} ({})".format(
                    str(enabled).lower(),
                    "Predbat Huawei TOU enabled" if enabled else "handoff/passive mode",
                )
            )
            self._last_control_enabled = enabled

        # IMPORTANT: huawei_tou=false is a hard handoff. Do not build/compare
        # or write a Predbat TOU plan while disabled. If Huawei is currently in
        # our native TOU mode, return it to maximise_self_consumption first.
        if not enabled:
            self._handoff_to_self_consumption("huawei_tou=false")
            return

        huawei_state = self.read_huawei_state()
        current = self.read_tou_periods()
        preview = self.build_control_preview()
        wanted = self.tou_preview_as_text(preview["periods"])

        # Run the idempotent live TOU test on every invocation so readback can
        # advance the staged transaction even when the Predbat plan is unchanged.
        self.write_tou_test(preview, current, huawei_state)

        action_signature = []
        for action in preview["actions"]:
            action_signature.append(
                (
                    action.get("kind"),
                    action.get("start"),
                    action.get("end"),
                    action.get("absolute_start"),
                    action.get("absolute_end"),
                    action.get("target_kwh"),
                    action.get("target_percent"),
                    action.get("runtime_action"),
                    action.get("car"),
                )
            )

        signature = (
            tuple(current) if current is not None else None,
            huawei_state.get("working_mode"),
            huawei_state.get("charge_from_grid"),
            huawei_state.get("excess_pv"),
            huawei_state.get("capacity_control"),
            tuple(wanted),
            tuple(action_signature),
            tuple(
                (
                    conflict["start"],
                    conflict["end"],
                    self._state_key(conflict["kept"]["state"]),
                    self._state_key(conflict["deferred"]["state"]),
                )
                for conflict in preview["conflicts"]
            ),
        )

        if signature == self._last_preview_signature:
            return
        self._last_preview_signature = signature

        self.log("Huawei PLAN TEST: ===========================================")
        self.log("Huawei PLAN TEST: V6.3 LIVE TOU TEST - future-only sparse 15m TOU +/- WRITES ENABLED; midnight is a hard split; true export remains preview-only")
        self.log_huawei_state_preview(huawei_state)
        self.log_tou_preview(preview)
        self.log_action_preview(preview)
        self.log_tou_compare(preview, current)
        self.log("Huawei PLAN TEST: ===========================================")
