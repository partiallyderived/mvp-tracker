from __future__ import annotations

import asyncio
import copy
import itertools
import json
import math
import os
import re
import sys
import time
import traceback
from asyncio import Lock, Task
from collections.abc import Callable, Iterable
from datetime import datetime, timedelta, timezone
from types import CodeType
from typing import Any, TypeVar

from discord import Client, Embed, Guild, Message, Role, TextChannel
from sortedcontainers import SortedDict, SortedSet

from default import DEFAULT

T = TypeVar('T')

HELP_MSG = """\
General Notes:
    For any command other than !track, you need to replace spaces with
        underscores.

    In, for example, !track <name> <time of death>, the words between
        "<" and ">" describe the arguments to submit to that command. A
        command may be described more than once if it has different behavior
        depending on how many arguments are passed.

    !t can be used instead of !track. Also works for e.g. !t-add instead of
    !track-add.
        
Commands:

!track: Refresh the list of tracked monsters.

!track <monster>: Begin tracking the monster of the given name assuming it died
   just as the command was entered. If the monster was already being tracked,
   that information is replaced.
Example: !track gtb

!track <monster> <time of death>: Begin tracking the monster of the given name.
    If <time of death> is in HH:MM format, assumes this is the server time the
    monster died. Otherwise, it is assumed to be the number of minutes ago the
    monster died. If the monster was already being tracked, that information is
    replaced.
Examples:
    GTB died at 5:30 server time: !track gtb 5:30
    Baphomet died 70 minutes ago: !track bapho 70

!track <monster> <alive time> <dead time>: Begin tracking the monster of the
    given name, assuming it was *alive* at <alive time> but dead at <dead time>,
    inferred via @checkboss. This version is not for use for monsters that leave
    a tombstone, just read the tombstone time directly in that case. If you
    cannot remember when you killed a monster, just give an estimate using 1
    time argument instead of using this version (e.g., use this version only
    when the window of death is *inferred* rather than *estimated*.) The reason
    for this is that for user estimates, we expect spawn times closer to the
    center of the estimate, while we do not for inferences.
Example ("Vocal was alive 30 minutes but dead 10 minutes ago"): !t vocal 30 10

!track <monster> ?: Begin tracking the monster of the given name assuming you
    just saw that it was dead via @checkboss. When no prior tracking information
    for this spawn is present, it is equivalent to
    !track monster <max spawn time> 0, i.e. !track amon 70 0. When prior
    tracking information *is* present, the window in which the monster could
    have died is adjusted accordingly.
Example ("I just saw Ghostring was dead via @checkboss"): !track gr ?

!track <monster> ? <time of death>: Same as above, but for when the monster was
    seen dead at the given time.
Example ("I saw Dragonfly was dead via @checkboss 15 minutes ago"):
    !track df ? 15

!track-add <monster> <map name> <min respawn minutes> <max respawn minutes>:
    Configure a new spawn to be trackable with the given name and min/max
    respawn times in minutes. The given name should be canonical but with spaces
    replaced by underscores (i.e., Golden_Thief_Bug). You can then add aliases
    using !track-edit if desired.
Example: !track-add Amon_Ra Pyramid 60 70

!track-add-editor <@user...>: Configure one or more users to be editors.
Example: !track-add-editor @User1 @User2

!track-alert <expression>: Configure the tracker to send an alert by posting a
    message to the tracking channel when the given expression is True. The given
    expression recognizes the variables min, max, now, and prob, where min and
    max are the minimum and maximum absolute spawn times, now is the current
    time, and prob is the probability (0 <= prob <= 1) that the monster has
    spawned. Must be a valid Python expression.
Example (Alert 2 minutes after monster could've spawned): !t-alert now - min > 2
Example (Alert when monster has at least 75% chance of being spawned):
    !t-alert prob > 0.75

!track-alert-role: Display the currently configured role for alerts, if any.

!track-alert-role <role> (editor only): Configure the given role to be
    mentioned whenever an alert goes off.

!track-auto-refresh: Display the amount of minutes after which the
    tracking information is refreshed.

!track-auto-refresh <minutes> (editor only): Set the auto-refresh time to the
    specified number of minutes.

!track-cancel <monsters...>: Cancel tracking for one or more monsters.
Example: !track-cancel gtb missy

!track-channel: Display the current tracking channel.

!track-channel <#channel> (editor only): Configure a channel to be the tracking
    channel. Note that all messages in the channel will be deleted whenever
    tracking information is updated. Use with caution.
Example: !track-channel #general

!track-conf: Display the current configurations, including all trackable 
    monsters. Arguments are ignored.

!track-edit <args...> (editor only): Edit the configuration for a trackable
    spawn (name, map, min respawn, max respawn, and aliases). Any combination
    may be edited at once with this command. Refer to examples for usage
    information.
Examples:
    Edit min and max respawn time for Amon Ra to be 30 and 50 minutes 
         respectively and edit map to be Pyramids:
         !track-edit amon min=30 max=50 map=Pyramids
    Edit name of "Silver Thief Bug" to "Golden Thief Bug" and add and 
         remove aliases: !track-edit Silver_Thief_Bug 
         name=Golden_Thief_Bug aliases+=gold,gtb aliases-=silver,stb

!track-expire: Display the current monster expiration time in minutes. After a
    monster has been spawned for at least this long, its tracking is cancelled.

!track-expire <new expire time> (editor only): Set the monster expiration time
    to the given time in minutes. Set to 0 to disable expiration, after which
    tracking will only be cancelled after it is replaced via !track or cancelled
    via !track-cancel.

!track-help: Display this help message. Arguments are ignored.

!track-remove <monster> (editor only): Set a spawn to no longer be trackable.
    For example, after submitting !track-remove gtb, !t gtb (or !t 
    Golden_Thief_Bug or another alias) will no longer work. This is the opposite
    of !track-add.

!track-remove-alert: Remove a configured alert. The user will be prompted to
    choose from a list of configured expressions (so submit with no arguments).

!track-remove-editor <@user...> (editor only): Remove editor privileges from one
    or  more users. This is the opposite of !track-add-editor.
Example: !track-remove-editor @Keele @Hixxy

!track-utc-offset: Display the current UTC offset of the server in HH:MM format
    with an optional leading minus sign.

!track-utc-offset <new offset> (editor only): Set the UTC offset of the server
    to the given offset in HH:MM format, optionally with a leading minus sign.
    A leading zero is allowed but not required for 1-digit hours.
Example (for when server time is US East): !track-utc-offset -04:00"""


BASE_EMBED_LEN = len('Enemy') + len('Up Time') + len('Up Now?')
BULK_DELETE_GRACE_SECONDS = 300
BULK_DELETE_DELTA = timedelta(days=14, seconds=-BULK_DELETE_GRACE_SECONDS)
CHANNEL_MENTION_RE = re.compile(r'<#(\d+)>')
CONF = 'config.json'
LOCK = Lock()
MAX_EMBED_SIZE = 6000
MAX_FIELD_SIZE = 1024
MAX_NAME_CHARS = 40
MAX_NAME_LEN = MAX_NAME_CHARS + 4 + 2 + 1
MAX_UP_TIME_LEN = len('**Within 1500~1550 Minutes**  \n')
MAX_LINE_LEN = MAX_NAME_LEN + 4 + MAX_UP_TIME_LEN + len('**100%**\n') + 1
MAX_BOSSES_PER_MSG = min(
    MAX_EMBED_SIZE // MAX_LINE_LEN - 1,
    MAX_FIELD_SIZE // max(MAX_NAME_LEN, MAX_UP_TIME_LEN)
)
ME = 194263402959339520
ROLE_MENTION_RE = re.compile(r'<@&(\d+)>')
USER_MENTION_RE = re.compile(r'<@(\d+)>')

EMPTY_EMBED = Embed()
EMPTY_EMBED.add_field(name='\u200b', value='\u200b')

client = Client()
global_config = {}
guild_to_state = {}

SpawnConfig = dict[str, bool | int | float]
BossConfig = dict[str, list[str] | dict[str, SpawnConfig]]
Config = dict[str, int | list[int] | list[str] | dict[str, BossConfig]]


class State:
    config: Config
    name_to_boss: SortedDict[str, set[str]]
    boss_set: SortedSet[str]
    tracked: dict[tuple[str, str], set[int]]
    last_msg: Message | None
    send_time: float
    guild: Guild | None
    disamb: dict[int, tuple[list, Callable, tuple]]
    auto_refresh_task: Task | None
    refresh_time: float
    alert_checks: list[CodeType]
    messages: list[Message]
    _alert_role: Role | None
    _channel: TextChannel | None

    @staticmethod
    def add_fields(
        embed: Embed,
        name_lines: list[str],
        up_time_lines: list[str],
        prob_lines: list[str],
        empty: bool
    ) -> None:
        if empty:
            name1, name2, name3 = '\u200b', '\u200b', '\u200b'
        else:
            name1, name2, name3 = 'Enemy', 'Up Time', 'Up Now?'
        embed.add_field(name=name1, value='\n'.join(name_lines))
        embed.add_field(name=name2, value='\n'.join(up_time_lines))
        embed.add_field(name=name3, value='\n'.join(prob_lines))

    @staticmethod
    def boss_key(boss: str) -> str:
        return boss.lower().replace(' ', '_')

    @staticmethod
    def calc_absent_prob(
        time_after: float, min_spawn: float, max_spawn: float
    ) -> float:
        if time_after <= min_spawn:
            inner = time_after * math.log(max_spawn / min_spawn)
        else:
            inner = time_after * math.log(
                max_spawn / time_after
            ) + time_after - min_spawn
        return inner / (max_spawn - min_spawn)

    @staticmethod
    def calc_window_prob(
        time_after: float, min_spawn: float, max_spawn: float, window: float
    ) -> float:
        if window == max_spawn:
            return State.calc_absent_prob(time_after, min_spawn, max_spawn)
        length = max_spawn - min_spawn
        inverse_time = max_spawn - time_after
        inverse_window = max_spawn - window
        result = 0.0
        gap = min_spawn - window
        if gap < 0:
            if time_after < window:
                if time_after <= min_spawn:
                    result += time_after * math.log(window / min_spawn)
                else:
                    result += time_after * math.log(window / time_after)
                    result += time_after - min_spawn
                if time_after < inverse_window:
                    result += time_after * time_after / (2 * window)
                else:
                    result += (
                        inverse_window * (2 * time_after - inverse_window)
                    ) / (2 * window)
            else:
                result += window - min_spawn
                if time_after < inverse_window:
                    result += time_after - window / 2
                else:
                    result += inverse_window - (
                        inverse_time * inverse_time
                    ) / 2 * window
        else:
            after_gap = time_after - gap
            if after_gap <= 0:
                return 0
            if time_after < min_spawn:
                if time_after < inverse_window:
                    result = after_gap * after_gap / (2 * window)
                else:
                    return (
                        2 * (time_after + window) - max_spawn - min_spawn
                    ) / (2 * window)
            elif time_after < inverse_window:
                result = (window + 2 * (time_after - min_spawn))
            else:
                result = length - (inverse_time * inverse_time) / (2 * window)
        return result / length

    @staticmethod
    def extract_disamb_range(
        args: list[str]
    ) -> tuple[list[str], list[int] | None]:
        if not args:
            return args, None
        disamb_idxs = State.parse_disamb_range(args[-1])
        if disamb_idxs is None:
            return args, None
        return args[:-1], disamb_idxs

    @staticmethod
    def parse_disamb_range(rng: str) -> list[int] | None:
        if rng.startswith("'"):
            if (value := int_or_none(rng[1:])) is None or value <= 0:
                return None
            return [value]
        comma_splits = rng.split(',')
        hyphen_splits_list = [s.split('-') for s in comma_splits]
        if len(comma_splits) == 1 and len(hyphen_splits_list[0]) == 1:
            return None
        result = set()
        for splits in hyphen_splits_list:
            if len(splits) == 1:
                if (value := int_or_none(splits[0])) is None or value <= 0:
                    return None
                if value <= 0:
                    return None
                result.add(value)
            elif len(splits) == 2:
                if (value1 := int_or_none(splits[0])) is None or (
                    value2 := int_or_none(splits[1])
                ) is None:
                    return None
                if (
                    value1 <= 0 or
                    value2 <= 0 or
                    value1 > value2 or
                    value2 > 1000
                ):
                    return None
                result.update(range(value1, value2 + 1))
            else:
                return None
        return sorted(result)

    def __init__(self, config: dict) -> None:
        self.config = config
        self.name_to_boss = SortedDict()
        self.boss_set = SortedSet()
        self.tracked = {
            (b, loc): set() for b in self.bosses for loc in self.spawns(b)
            if self.is_tracked(b, loc)
        }

        self.last_msg = None
        self.send_time = 0
        self.guild = None
        self.disamb = {}
        self.auto_refresh_task = None
        self.refresh_time = time.time() / 60
        self.messages = []
        self._alert_role = None
        self._channel = None
        self.alert_checks = []
        for alert in config['alerts']:
            self.alert_checks.append(compile(alert, '<string>', 'eval'))

    @staticmethod
    def eval_condition(
        code: CodeType,
        *,
        now: float,
        min_time: float,
        max_time: float,
        prob: float
    ) -> bool:
        return eval(
            code,
            {'__builtins__': None},
            {'now': now, 'min': min_time, 'max': max_time, 'prob': prob}
        )

    @property
    def alert_role(self) -> Role | None:
        if self._alert_role:
            return self._alert_role
        role_id = self.config.get('alert-role')
        if not role_id:
            return None
        self._alert_role = self.guild.get_role(role_id)
        return self._alert_role

    @alert_role.setter
    def alert_role(self, value: Role) -> None:
        self.config['alert-role'] = value.id
        self._alert_role = value

    @property
    def alerts(self) -> list[str]:
        return self.config['alerts']

    @property
    def alerts_str(self) -> str:
        if not self.alerts:
            return ' None'
        components = ['']
        for a in self.alerts:
            components.append(a)
        return '\n'.join(components)

    @property
    def auto_refresh(self) -> int:
        return self.config['auto-refresh']

    @auto_refresh.setter
    def auto_refresh(self, value: int) -> None:
        self.config['auto-refresh'] = value

    @property
    def auto_refresh_str(self) -> str:
        auto_refresh = self.auto_refresh
        if not auto_refresh:
            return 'unset'
        return quantity('minute', auto_refresh)

    @property
    def bosses(self) -> dict[str, BossConfig]:
        return self.config['bosses']

    @property
    def channel(self) -> TextChannel | None:
        if self._channel:
            return self._channel
        channel_id = self.config.get('channel')
        if not channel_id:
            return None
        self._channel = client.get_channel(channel_id)
        return self._channel

    @channel.setter
    def channel(self, value: TextChannel) -> None:
        self._channel = value
        self.config['channel'] = value.id
        self.messages = []

    @property
    def channel_str(self) -> str:
        if channel_id := self.channel:
            return f'<#{channel_id}>'
        return 'unset'

    @property
    def expire_time(self) -> int:
        return self.config['expire']

    @expire_time.setter
    def expire_time(self, value: int) -> None:
        self.config['expire'] = value

    @property
    def expire_time_str(self) -> str:
        return quantity(
            'minute', self.expire_time
        ) if self.expire_time else 'unset'

    @property
    def utc_offset(self) -> int:
        return self.config['utc-offset']

    @utc_offset.setter
    def utc_offset(self, value: int) -> None:
        self.config['utc-offset'] = value

    @property
    def utc_offset_str(self) -> str:
        return minutes_to_hhmm(self.utc_offset)

    def aliases(self, boss: str) -> list[str]:
        return self.boss_conf(boss)['aliases']

    def spawns(self, boss: str) -> dict[str, SpawnConfig]:
        return self.boss_conf(boss)['spawns']

    def max(self, boss: str, loc: str) -> int:
        return self.spawn(boss, loc)['max']

    def min(self, boss: str, loc: str) -> int:
        return self.spawn(boss, loc)['min']

    def tod(self, boss: str, loc: str) -> float | None:
        return self.spawn(boss, loc).get('tod')

    def window(self, boss: str, loc: str) -> float:
        return self.spawn(boss, loc)['window']

    def set_aliases(self, boss: str, aliases: set[str]) -> None:
        self.boss_conf(boss)['aliases'] = sorted(
            aliases, key=lambda x: (len(x), x)
        )
        for name in self.names(boss):
            self.name_to_boss.setdefault(name, set()).add(boss)

    def set_max(self, boss: str, loc: str, value: int) -> None:
        self.spawn(boss, loc)['max'] = value

    def set_min(self, boss: str, loc: str, value: int) -> None:
        self.spawn(boss, loc)['min'] = value

    def set_tod(
        self, boss: str, loc: str, value: float, window: float
    ) -> None:
        self.spawn(boss, loc)['tod'] = value
        self.spawn(boss, loc)['window'] = window

    def add(
        self, boss: str, config: BossConfig, add_implicit_aliases: bool
    ) -> None:
        all_aliases = set(config['aliases'])
        if add_implicit_aliases:
            if ' ' in boss:
                all_aliases.add(boss.lower().replace(' ', ''))
                all_aliases.add(''.join(s[0].lower() for s in boss.split()))
        self.boss_set.add(boss)
        self.bosses[boss] = config
        self.set_aliases(boss, all_aliases)

    def add_alert(self, now: float, code_string: str, code: CodeType) -> None:
        self.alert_checks.append(code)
        # noinspection PyTypeChecker
        self.config['alerts'].append(code_string)
        for (boss, loc), future_alerts in self.tracked.items():
            i = len(self.alert_checks) - 1
            min_time, max_time, prob = self.spawn_info(boss, loc)
            if not self.eval_condition(
                self.alert_checks[i],
                now=now,
                min_time=min_time,
                max_time=max_time,
                prob=prob
            ):
                # Only add alert for monsters for which it is not already true.
                future_alerts.add(i)

    async def add_message(self, message: Message) -> None:
        self.messages.append(message)

    def alerts_msg(self) -> str:
        components = []
        alerts = self.alerts
        for (boss, loc), future_alerts in self.tracked.items():
            for i in self.new_alerts(self.refresh_time, boss, loc):
                future_alerts.remove(i)
                components.append(f'{self.boss_label(boss, loc)}: {alerts[i]}')
        if not components:
            return ''
        if role := self.alert_role:
            components.append(role.mention)
        return '\n'.join(components)

    def boss_conf(self, boss: str) -> BossConfig:
        return self.bosses[boss]

    def boss_info(self, boss: str) -> str:
        aliases = self.aliases(boss)
        alias_str = (
            f' (aka {", ".join(x for x in aliases)})' if aliases else ''
        )
        spawns = self.spawns(boss)
        if len(spawns) == 1:
            spawn = first(spawns)
            return (
                f'{boss}{alias_str}: '
                f'{self.min(boss, spawn)}~{self.max(boss, spawn)}'
            )
        all_spawn_info = '\n    '.join(
            self.spawn_str(boss, loc) for loc in sorted(spawns)
        )
        return f'{boss}{alias_str}:\n    {all_spawn_info}'

    def boss_label(self, boss: str, loc: str) -> str:
        return boss if len(self.spawns(boss)) == 1 else f'{boss} ({loc})'

    def boss_sort_key(self, boss: str, loc: str) -> tuple[float, float]:
        min_time, max_time, prob = self.spawn_info(boss, loc)
        if self.expire_time and self.refresh_time - max_time > self.expire_time:
            return 1, min_time
        return -prob, min_time

    def cancel(self, boss: str, loc: str) -> bool:
        if self.tracked.pop((boss, loc), None) is not None:
            del self.spawn(boss, loc)['tod']
            del self.spawn(boss, loc)['window']
            return True
        return False

    def check_expire(self, boss: str, loc: str) -> bool:
        if not self.expire_time:
            return False
        _, max_spawn = self.spawn_time(boss, loc)
        if (
            self.refresh_time - self.tod(boss, loc)
            > max(2 * max_spawn, self.expire_time)
        ):
            self.cancel(boss, loc)
            return True
        return False

    async def disambiguate(self, i: int) -> str | None:
        i -= 1
        if disamb_info := self.disamb.get(self.last_msg.author.id, None):
            options, fn, args = disamb_info
            if i >= len(options):
                return None
            del self.disamb[self.last_msg.author.id]
            result = await fn(self, options[i], *args)
            save()
            return result
        return None

    def disambiguation_prompt(
        self,
        msg: str,
        options: list[tuple[str, Any]],
        fn: Callable,
        args: tuple = (),
        sort: bool = True
    ) -> str:
        if sort:
            options = sorted(
                options, key=lambda x: x[0].replace('(', '').replace(')', '')
            )
        str_options, options = zip(*options)
        self.disamb[self.last_msg.author.id] = options, fn, args
        self.refresh_time = time.time() / 60
        return f'{msg}\n\n' + '\n'.join(
            f'{i}) {opt}' for i, opt in enumerate(str_options, 1)
        )

    def embeds(self) -> list[Embed]:
        embeds = []
        total_chars = BASE_EMBED_LEN
        total_name_chars = 0
        total_up_time_chars = 0
        name_lines = []
        up_time_lines = []
        prob_lines = []
        embed = Embed()
        first_fields = True
        for boss, loc in [
            (x, loc) for x, loc in sorted(
                self.tracked, key=lambda z: self.boss_sort_key(z[0], z[1])
            )
            if not self.check_expire(x, loc)
        ]:
            should_reset = False
            name, up_time, prob = self.tracking_line(boss, loc)
            name_len = len(name) + 1
            up_time_len = len(up_time) + 1
            prob_len = len(prob) + 1
            total_chars += name_len + up_time_len + prob_len
            total_name_chars += name_len + 1
            total_up_time_chars += up_time_len + 1

            if total_chars >= MAX_EMBED_SIZE:
                self.add_fields(
                    embed,
                    name_lines,
                    up_time_lines,
                    prob_lines,
                    not first_fields
                )
                first_fields = False
                embeds.append(embed)
                total_chars = name_len + up_time_len + prob_len
                should_reset = True
                embed = Embed()
            elif max(total_name_chars, total_up_time_chars) >= MAX_FIELD_SIZE:
                self.add_fields(
                    embed,
                    name_lines,
                    up_time_lines,
                    prob_lines,
                    not first_fields
                )
                first_fields = False
                should_reset = True
            if should_reset:
                name_lines.clear()
                up_time_lines.clear()
                prob_lines.clear()
                total_name_chars = name_len
                total_up_time_chars = up_time_len
            name_lines.append(name)
            up_time_lines.append(up_time)
            prob_lines.append(prob)
        if name_lines:
            self.add_fields(
                embed, name_lines, up_time_lines, prob_lines, not first_fields
            )
            embeds.append(embed)
        return embeds

    def first_spawn(self, bosses: set[str]) -> tuple[str, str]:
        boss = first(bosses)
        return boss, first(self.spawns(boss))

    def format_time(self, t: float) -> str:
        time_obj = time.gmtime(60 * (t + self.utc_offset))
        return f'{time_obj.tm_hour:02d}:{time_obj.tm_min:02d}'

    def is_editor(self, member: int | None = None) -> bool:
        if member is None:
            member = self.last_msg.author
        else:
            member = (
                [m for m in self.last_msg.channel.members if m.id == member][0]
            )
        return (
            member.id in self.config['editors']
            or member.guild_permissions.manage_guild
        )

    def is_tracked(self, boss: str, loc: str) -> bool:
        return self.tod(boss, loc) is not None

    def names(self, boss: str) -> set[str]:
        return set(itertools.chain(self.aliases(boss), [self.boss_key(boss)]))

    def new_alerts(self, now: float, boss: str, loc: str) -> set[int]:
        min_time, max_time, prob = self.spawn_info(boss, loc)
        result = set()
        for i in self.tracked[boss, loc]:
            if self.eval_condition(
                self.alert_checks[i],
                now=now,
                min_time=min_time,
                max_time=max_time,
                prob=prob
            ):
                result.add(i)
        return result

    def parse_time(self, text: str) -> float | None:
        minutes = parse_time(text)
        if minutes is None or minutes < 0:
            return None
        now = self.send_time
        if ':' in text:
            minutes += self.utc_offset
            time_obj = time.gmtime(now * 60)
            now_minutes = (
                time_obj.tm_sec / 60 + time_obj.tm_min + 60 * time_obj.tm_hour
            )
            return now - abs(now_minutes - minutes)
        return now - minutes

    async def purge_channel(self) -> None:
        channel = self.channel
        cutoff = datetime.utcnow() - BULK_DELETE_DELTA
        bulk_deletable = []
        message_ids = set(m.id for m in self.messages)
        awaitables = []
        async for msg in channel.history(limit=None):
            if msg.id in message_ids:
                continue
            if msg.created_at > cutoff:
                bulk_deletable.append(msg)
                if len(bulk_deletable) == 100:
                    awaitables.append(asyncio.create_task(
                        channel.delete_messages(bulk_deletable)
                    ))
                    bulk_deletable.clear()
            else:
                awaitables.append(asyncio.create_task(msg.delete()))
        if bulk_deletable:
            awaitables.append(
                asyncio.create_task(channel.delete_messages(bulk_deletable))
            )
        for awaitable in awaitables:
            await awaitable

    async def refresh(self) -> None:
        channel = self.channel
        if not channel:
            return
        self.refresh_time = time.time() / 60
        alerts_msg = self.alerts_msg()
        embeds = self.embeds()
        tasks = []
        for _ in range(len(self.messages) - len(embeds)):
            self.messages.pop()
        for _ in range(len(embeds) - len(self.messages)):
            await self.add_message(await channel.send(embed=EMPTY_EMBED))
        for embed, message in zip(embeds, self.messages):
            tasks.append(asyncio.create_task(message.edit(embed=embed)))
        for task in tasks:
            await task
        await self.purge_channel()
        if alerts_msg:
            for embed in embed_splits(alerts_msg, 'Alerts'):
                await channel.send(embed=embed)

    def remove(self, boss: str, loc: str) -> bool:
        cancelled = self.cancel(boss, loc)
        spawns = self.spawns(boss)
        del spawns[loc]
        if not spawns:
            self.boss_set.remove(boss)
            self.remove_aliases(boss)
            del self.bosses[boss]
        return cancelled

    def remove_alert(self, i: int) -> None:
        del self.alerts[i]
        del self.alert_checks[i]
        for future_alerts in self.tracked.values():
            future_alerts.discard(i)
            decrement = {j for j in future_alerts if j > i}
            future_alerts -= decrement
            future_alerts |= {j - 1 for j in decrement}

    def remove_aliases(self, boss: str) -> None:
        for alias in self.names(boss):
            bosses = self.name_to_boss[alias]
            bosses.remove(boss)
            if not bosses:
                del self.name_to_boss[alias]

    def resolve(self, name: str) -> set[str]:
        name = name.replace(' ', '_').lower()
        idx = self.name_to_boss.bisect_left(name)
        items = self.name_to_boss.items()
        bosses = set()

        # noinspection PyUnresolvedReferences
        while idx < len(self.name_to_boss) and items[idx][0].startswith(name):
            # noinspection PyUnresolvedReferences
            full, new_bosses = self.name_to_boss.items()[idx]
            if full == name:
                return set(new_bosses)
            bosses |= new_bosses
            idx += 1
        return bosses

    def resolve_tracked(self, name: str) -> list[tuple[str, str]]:
        bosses = self.resolve(name)
        return sorted(
            (b, loc) for b in bosses for loc in self.spawns(b)
            if (b, loc) in self.tracked
        )

    async def schedule_refresh(self) -> None:
        sleep_time = max(
            0.0,
            60 * (self.auto_refresh + self.refresh_time) - time.time()
        )
        if sleep_time:
            await asyncio.sleep(sleep_time)
        async with LOCK:
            since_last = time.time() / 60 - self.refresh_time
            if since_last >= self.auto_refresh - 0.001:
                await self.refresh()
            self.auto_refresh_task = asyncio.create_task(
                self.schedule_refresh()
            )

    def spawn(self, boss: str, loc: str) -> SpawnConfig:
        return self.spawns(boss)[loc]

    def spawn_info(self, boss: str, loc: str) -> tuple[float, float, float]:
        tod = self.tod(boss, loc)
        min_spawn, max_spawn = self.spawn_time(boss, loc)
        window = self.window(boss, loc)
        min_time = tod + max(0.0, min_spawn - window)
        max_time = tod + max_spawn
        if self.refresh_time >= max_time:
            return min_time, max_time, 1
        if self.refresh_time <= min_time:
            return min_time, max_time, 0
        if window and min_spawn != max_spawn:
            prob = self.calc_window_prob(
               self.refresh_time - tod, min_spawn, max_spawn, window
            )
        else:
            prob = (self.refresh_time - min_time) / (max_time - min_time)
        return min_time, max_time, prob

    def spawn_options(
        self, bosses: set[str]
    ) -> list[tuple[str, tuple[str, str]]]:
        return sorted([
            (self.boss_label(b, loc), (b, loc))
            for b in bosses for loc in self.spawns(b)
        ], key=lambda x: x[0].replace('(', '').replace(')', ''))

    def spawn_str(self, boss: str, loc: str) -> str:
        min_spawn, max_spawn = self.spawn_time(boss, loc)
        dur = (
            str(min_spawn) if min_spawn == max_spawn
            else f'{min_spawn}~{max_spawn}'
        )
        return f'{loc}: {dur}'

    def spawn_time(self, boss: str, loc: str) -> tuple[int, int]:
        return self.min(boss, loc), self.max(boss, loc)

    def track(
        self, boss: str, loc: str, tod: float, window: float | None
    ) -> None:
        self.cancel(boss, loc)
        self.set_tod(boss, loc, tod, window)
        self.tracked[boss, loc] = set(range(len(self.alert_checks)))

        # Don't alert for conditions that are already true.
        self.tracked[boss, loc] -= self.new_alerts(tod, boss, loc)

    def tracking_line(self, boss: str, loc: str) -> tuple[str, str, str]:
        name = self.boss_label(boss, loc)
        if len(name) > MAX_NAME_CHARS:
            name = f'{name[:9]}...{name[-8:]}'
        now = self.refresh_time
        min_time, max_time, prob = self.spawn_info(boss, loc)
        since_min = round(now - min_time)
        since_max = round(now - max_time)
        abs_since_min = abs(since_min)
        abs_since_max = abs(since_max)
        left = min(abs_since_min, abs_since_max)
        right = max(abs_since_min, abs_since_max)
        prob_str = f'{str(math.floor(prob * 100))}%'
        if since_min == since_max or (since_max < 0 < since_min):
            minute_str = quantity('Minute', abs_since_max)
        else:
            minute_str = f'{left}~{right} Minutes  '
        if since_min < 0:
            status = f'In {minute_str}  '
        elif since_max < 0:
            status = f'Within {minute_str}  '
        else:
            name = f'**{name}**'
            status = f'**{minute_str} Ago**  '
            prob_str = f'**{prob_str}**'
        name = f'{name}  '
        return name, status, prob_str

    def unambiguous(self, bosses: set[str]) -> bool:
        return len(bosses) == 1 and len(self.spawns(first(bosses))) == 1

    def update_boss(
        self, boss: str, new_name: str, new_aliases: set[str]
    ) -> None:
        self.remove_aliases(boss)

        if new_name != boss:
            for loc in self.spawns(boss):
                if (alerts := self.tracked.pop((boss, loc), None)) is not None:
                    self.tracked[new_name, loc] = alerts
            self.boss_set.remove(boss)
            self.boss_set.add(new_name)
            self.bosses[new_name] = self.bosses.pop(boss)

        self.set_aliases(new_name, new_aliases)

    def update_spawn(
        self,
        boss: str,
        loc: str,
        new_name: str,
        new_map: str,
        new_min: int,
        new_max: int,
        new_aliases: set[str]
    ) -> None:
        self.set_min(boss, loc, new_min)
        self.set_max(boss, loc, new_max)

        if new_map != loc:
            self.spawns(boss)[new_map] = self.spawns(boss).pop(loc)
            if (alerts := self.tracked.pop((boss, loc), None)) is not None:
                self.tracked[boss, new_map] = alerts
        self.update_boss(boss, new_name, new_aliases)


def _fail(fail_msg: str, reason: str) -> str:
    return f'{fail_msg}: {reason}'


def first(it: Iterable[T]) -> T:
    return next(iter(it))


async def init_state(guild: str) -> State:
    config = copy.deepcopy(DEFAULT)
    global_config[guild] = config
    state = State(config)
    load_state(guild, state, True)
    state.auto_refresh_task = asyncio.create_task(state.schedule_refresh())
    return state


def int_or_none(arg: str) -> int | None:
    try:
        return int(arg)
    except ValueError:
        return None


def load_state(guild: str, state: State, add_aliases: bool) -> None:
    guild_to_state[guild] = state
    for boss_name, boss_config in state.bosses.items():
        state.add(boss_name, boss_config, add_aliases)


def minutes_to_hhmm(minutes: int) -> str:
    sign, hours, minutes = sign_hr_min_split(minutes)
    minus_maybe = '-' if sign else ''
    return f'{minus_maybe}{hours:02d}:{minutes:02d}'


def parse_channel_mention(txt: str) -> int | None:
    match = CHANNEL_MENTION_RE.match(txt)
    if not match:
        return None
    return int_or_none(match.group(1))


def parse_role_mention(txt: str) -> int | None:
    match = ROLE_MENTION_RE.match(txt)
    if not match:
        return None
    return int_or_none(match.group(1))


def parse_user_mention(txt: str) -> int | None:
    match = USER_MENTION_RE.match(txt)
    if not match:
        return None
    return int_or_none(match.group(1))


def parse_time(txt: str) -> int | None:
    negate = txt.startswith('-')
    if negate:
        txt = txt[1:]
    splits = txt.split(':')
    if len(splits) > 2:
        return None
    if len(splits) == 2:
        if not splits[0] or len(splits[0]) > 2 or len(splits[1]) != 2:
            return None
        if not all(d.isdigit() for d in splits[0]):
            return None
        hours = int(splits[0])
    else:
        hours = 0
    if hours >= 24:
        return None
    if not splits[-1] or not all(d.isdigit() for d in splits[-1]):
        return None
    minutes = int(splits[-1])
    if len(splits) == 2 and minutes >= 60:
        return None
    minutes += 60 * hours
    if negate:
        minutes = -minutes
    return minutes


def quantity(name: str, amount: int) -> str:
    s_maybe = '' if amount == 1 else 's'
    return f'{amount} {name}{s_maybe}'


def save() -> None:
    with open(CONF, 'w') as f:
        json.dump(global_config, f)


def next_chunk(
    i: int, lines: list[str], max_len: int, chunk_lines: list[str]
) -> int:
    chunk_len = 0
    while i < len(lines) and chunk_len < max_len - len(lines[i]) - 1:
        line = lines[i]
        chunk_lines.append(line)
        chunk_len += len(line) + 1
        i += 1
    return i


def embed_splits(msg: str, title: str) -> list[Embed]:
    lines = msg.split('\n')
    chunk_lines = []
    max_len = 1024
    embeds = []
    i = 0
    num_fields = 0
    while i < len(lines):
        embed = Embed()
        while num_fields < 5 and i < len(lines):
            i = next_chunk(i, lines, max_len, chunk_lines)
            msg = '\n'.join(chunk_lines)
            embed.add_field(name=title, value=msg)
            title = '\u200b'
            chunk_lines.clear()
            num_fields += 1
        embeds.append(embed)
        num_fields = 0
    return embeds


async def send_chunked(channel: TextChannel, msg: str) -> None:
    code = msg.startswith('```\n') and msg.endswith('\n```')
    max_len = 2000 - 8 * code
    if len(msg) <= max_len:
        await channel.send(msg)
        return

    if code:
        msg = msg[4:-4]
    lines = msg.split('\n')
    chunk_lines = []
    i = 0
    while i < len(lines):
        if code:
            chunk_lines.append('```')
        i = next_chunk(i, lines, max_len, chunk_lines)
        if code:
            chunk_lines.append('```')
        msg = '\n'.join(chunk_lines)
        chunk_lines.clear()
        await channel.send(msg)


def sign_hr_min_split(minutes: int) -> tuple[bool, int, int]:
    if sign := minutes < 0:
        minutes = -minutes
    return sign, minutes // 60, minutes % 60


@client.event
async def on_message(message: Message) -> None:
    if message.author == client.user:
        return
    async with LOCK:
        try:
            guild = str(message.guild.id)
            state = guild_to_state.get(guild) or await init_state(guild)
            state.guild = message.guild
            state.last_msg = message
            state.send_time = datetime.timestamp(
                message.created_at.replace(tzinfo=timezone.utc)
            ) / 60
            args = message.content.split()
            if not args:
                return
            cmd = args[0]
            if not cmd.startswith('!'):
                if len(args) != 1:
                    return

                if not (disamb_idx := int_or_none(cmd)):
                    if not (
                        disamb_info := state.disamb.get(message.author.id)
                    ):
                        return
                    options, fn, args = disamb_info
                    if not (
                        fn is do_track
                        and (
                            disamb_idxs := State.parse_disamb_range(cmd)
                        )
                        and disamb_idxs[-1] <= len(options)
                    ):
                        return
                    tod, window = args[:2]
                    multi_options = [options[i - 1] for i in disamb_idxs]
                    if msg := await do_track_multi(
                        state, multi_options, tod, window
                    ):
                        await message.channel.send(msg)

                elif msg := await state.disambiguate(disamb_idx):
                    await message.channel.send(msg)
                return
            cmd = cmd[1:]
            if cmd == 't' or cmd.startswith('t-'):
                cmd = f'track{cmd[1:]}'
            if not (fn := CMD_TO_FN.get(cmd)):
                return
            author = message.author
            args = args[1:]
            if fn in NEEDS_EDITOR and not state.is_editor() and args:
                await message.channel.send(
                    f'!{cmd} failed: {author.name} is not an editor'
                )
                return
            resp = await fn(state, args)
            save()
            if resp:
                await send_chunked(message.channel, resp)
        except Exception:
            print(traceback.format_exc(), file=sys.stderr)
            await send_chunked(
                message.channel, f'Error:\n{traceback.format_exc()}'
            )


@client.event
async def on_disconnect() -> None:
    print(
        f'[{datetime.now().strftime("%m/%d at %I:%M %p")}] Got disconnected =(',
        file=sys.stderr
    )


@client.event
async def on_ready() -> None:
    async with LOCK:
        for state in guild_to_state.values():
            if not state.auto_refresh_task and state.auto_refresh:
                state.auto_refresh_task = asyncio.create_task(
                    state.schedule_refresh()
                )
    print('Ready!', file=sys.stderr)


async def handle_add(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to add boss', reason)

    if len(args) < 4:
        return fail(
            'expected exactly 4 arguments '
            '(name, map, min spawn time in minutes, max spawn time in minutes)'
        )
    name, map_name, min_spawn, max_spawn = args
    name = name.replace('_', ' ')
    map_name = map_name.replace('_', ' ')

    if (min_spawn := int_or_none(min_spawn)) is None:
        return fail(f'given min respawn time "{min_spawn}" is not an integer')
    if min_spawn < 0:
        return fail('given min respawn time is negative')

    if (max_spawn := int_or_none(max_spawn)) is None:
        return fail(f'given max respawn time "{max_spawn}" is not an integer')
    if max_spawn < 0:
        return fail(f'given max respawn time is negative')

    config = {
        'min': min_spawn,
        'max': max_spawn
    }

    bosses = state.resolve(name)
    if not bosses:
        return await do_add(state, (name, True), map_name, config)
    if len(bosses) == 1:
        return await do_add(state, (bosses.pop(), False), map_name, config)
    options = sorted(
        [(b, (b, False)) for b in bosses],
        key=lambda x: x[0].replace('(', '').replace(')', '')
    )
    options.append((f'New enemy named "{name}"', (name, True)))
    return state.disambiguation_prompt(
        f'Which enemy do you mean by "{args[0]}"?',
        options,
        do_add,
        (map_name, config),
        sort=False
    )


async def do_add(
    state: State, boss_and_is_new: tuple[str, bool], loc: str, config: dict
) -> str:
    boss, is_new = boss_and_is_new
    if is_new:
        config = {'aliases': [], 'spawns': {loc: config}}
        state.add(boss, config, add_implicit_aliases=True)
        return f'Successfully added enemy: {state.boss_info(boss)}'
    if loc in state.spawns(boss):
        return _fail(
            'Failed to add spawn',
            f'{loc} is already the name of a spawn for {boss}'
        )
    state.spawns(boss)[loc] = config
    return f'Successfully added spawn for boss: {state.boss_info(boss)}'


async def handle_add_editor(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to add editor', reason)

    if not args:
        return fail('No user mentions given')

    components = []
    for arg in args:
        mem_id = parse_user_mention(arg)
        if not mem_id:
            components.append(fail(f'{arg} is not a user mention'))
        else:
            if mem_id not in state.config['editors']:
                state.config['editors'].append(mem_id)
                components.append(f'Successfully added {arg} as an editor')
            else:
                components.append(fail(f'{arg} is already an editor'))
    return '\n'.join(components)


async def handle_alert(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to add alert', reason)

    if not args:
        return f'```\nConfigured alerts:{state.alerts_str}\n```'

    expr = ' '.join(args)
    try:
        code = compile(expr, '<string>', 'eval')
    except Exception:
        return fail('alert expression could not be compiled')

    test_now = 15
    test_min = 10
    test_max = 20
    test_prob = 0

    try:
        result = state.eval_condition(
            code,
            now=test_now,
            min_time=test_min,
            max_time=test_max,
            prob=test_prob
        )
    except Exception:
        return fail('alert expression errored on test case')
    if type(result) != bool:
        return fail('alert expression is not a boolean')

    state.add_alert(state.send_time, expr, code)
    return 'Successfully added alert'


async def handle_alert_role(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to set alert role', reason)

    if len(args) >= 2:
        return fail('expected at most 1 argument')

    if not args:
        role = state.alert_role
        string = 'not configured' if role is None else role.mention
        return f'Alert role: {string}'

    role_id = parse_role_mention(args[0])
    if not role_id:
        return fail(f'{args[0]} is not a role mention')

    state.alert_role = state.guild.get_role(role_id)
    return 'Successfully configured alert role'


async def handle_auto_refresh(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to set auto refresh time', reason)

    if not args:
        return (
            f'Tracking information auto-refresh time: {state.auto_refresh_str}'
        )

    if len(args) > 1:
        return fail('expected at most 1 argument')

    if (minutes := int_or_none(args[0])) is None:
        return fail('expected an integer')

    state.auto_refresh = minutes
    if state.auto_refresh_task:
        state.auto_refresh_task.cancel()
        state.auto_refresh_task = None
    if minutes:
        state.auto_refresh_task = asyncio.create_task(state.schedule_refresh())
        return f'Updated auto-refresh time to {state.auto_refresh_str}'
    if not minutes:
        return 'Auto-refresh disabled'


async def handle_cancel(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to cancel', reason)

    if not args:
        return fail('no boss names given')

    if not state.tracked:
        return fail('nothing is being tracked')

    if len(args) == 1 and args[0].lower() == 'all':
        for boss, loc in set(state.tracked):
            state.cancel(boss, loc)
        await state.refresh()
        return 'Successfully cancelled all tracked bosses'

    had_success = False
    components = []
    for arg in args:
        spawns = state.resolve_tracked(arg)
        if not spawns:
            components.append(fail(
                f'no boss aliased by {arg} is currently being tracked')
            )
            continue
        if len(spawns) == 1:
            boss, loc = first(spawns)
            if state.cancel(boss, loc):
                components.append(
                    f'Successfully cancelled {state.boss_label(boss, loc)}'
                )
            else:
                components.append(fail(
                    f'{state.boss_label(boss, loc)} '
                    f'not currently being tracked'
                ))
        elif len(args) == 1:
            return state.disambiguation_prompt(
                'Which spawn should be cancelled?',
                [(state.boss_label(b, loc), (b, loc)) for b, loc in spawns],
                do_cancel
            )
        else:
            components.append(fail(
                f'{arg} is ambiguous. To disambiguate, cancel {arg} only: '
                f'!track-cancel {arg}')
            )
    if had_success:
        await state.refresh()
    return '\n'.join(components)


async def do_cancel(state: State, spawn: tuple[str, str]) -> str:
    boss, loc = spawn
    if state.cancel(boss, loc):
        await state.refresh()
        return f'Successfully cancelled {state.boss_label(boss, loc)}'
    return _fail(
        f'Failed to cancel {state.boss_label(boss, loc)}',
        'not currently tracked'
    )


async def handle_channel(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to set channel', reason)

    if not args:
        return f'Tracking channel: {state.channel_str}'

    if len(args) > 1:
        return fail('expected at most one argument')

    channel_id = parse_channel_mention(args[0])
    if channel_id is None:
        return fail(f'{args[0]} is not a channel mention')

    state.channel = client.get_channel(channel_id)
    return f'MVP tracking channel now set to {args[0]}'


async def handle_conf(state: State, args: list[str]) -> str:
    if args:
        preamble = 'Note: arguments ignored\n'
    else:
        preamble = ''

    return (
        f'```\n{preamble}'
        f'Channel: {state.channel_str}\n'
        f'Auto-refresh time: {state.auto_refresh_str}\n' 
        f'Expire time: {state.expire_time_str}\n'
        f'Server time UTC offset: {state.utc_offset_str}\n\n'
        f'Alerts:{state.alerts_str}\n\n'
        f'Trackable monsters:\n'
        + '\n'.join(state.boss_info(b) for b in state.boss_set)
        + '\n```'
    )


async def handle_edit(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to edit', reason)

    if not args:
        return fail('no boss given')

    name, edits = args[0], args[1:]
    bosses = state.resolve(name)

    if not bosses:
        return fail(f'{name} is not a recognized boss or alias')

    if not edits:
        return fail(f'no edits requested')

    new_min = None
    new_map = None
    new_max = None
    new_name = None
    aliases_to_add = set()
    aliases_to_remove = set()
    new_aliases = set()

    for e in edits:
        splits = e.split('=')

        if len(splits) != 2:
            return fail(
                f'{e} is not formatted correctly (should be property=new)'
            )

        key, value = splits
        key = key.lower()

        if key == 'min' or key == 'max':
            if (value := int_or_none(value)) is None:
                return fail(f'expected integer for {key} respawn time')
            if value <= 0:
                return fail(f'{key} respawn time must be positive')

            if key == 'min':
                new_min = value
            else:
                new_max = value

        elif key == 'name':
            new_name = value.replace('_', ' ')

        elif key == 'map':
            new_map = value.replace('_', ' ')

        elif key.startswith('aliases'):
            if len(key) > 8 or len(key) == 8 and key[-1] not in {'-', '+'}:
                return fail(f'unrecognized property "{key}"')

            splits = set(x.lower() for x in value.split(','))
            if any('=' in x for x in splits):
                return fail('aliases may not contain "="')

            if len(key) == 7:
                new_aliases = splits
            elif key[-1] == '+':
                aliases_to_add |= splits
            else:
                aliases_to_remove -= splits
        else:
            return fail(f'unrecognized property "{key}"')

    if new_aliases and (aliases_to_add or aliases_to_remove):
        return fail(
            f'cannot set aliases and add/remove aliases at the same time'
        )

    if not (new_max or new_min or new_map):
        if len(bosses) == 1:
            return await do_edit_boss(
                state,
                first(bosses),
                new_name,
                new_aliases,
                aliases_to_add,
                aliases_to_remove
            )
        return state.disambiguation_prompt(
            'Which monster do you want to edit?',
            [(b, b) for b in bosses],
            do_edit_boss,
            (new_name, new_aliases, aliases_to_add, aliases_to_remove)
        )

    if state.unambiguous(bosses):
        return await do_edit_spawn(
            state,
            state.first_spawn(bosses),
            new_name,
            new_map,
            new_min,
            new_max,
            new_aliases,
            aliases_to_add,
            aliases_to_remove
        )

    return state.disambiguation_prompt(
        'Which spawn do you want to edit?',
        state.spawn_options(bosses),
        do_edit_spawn,
        (
            new_name,
            new_map,
            new_min,
            new_max,
            new_aliases,
            aliases_to_add,
            aliases_to_remove
        )
    )


def _new_aliases(
    state: State,
    boss: str,
    new_name: str | None,
    new_aliases: set[str],
    aliases_to_add: set[str],
    aliases_to_remove: set[str]
) -> str | set[str]:
    if new_name and boss != new_name and new_name in state.bosses:
        return _fail(
            'Failed to edit', f'"{new_name}" is already the name of a boss'
        )

    if not new_aliases:
        new_aliases = set(state.aliases(boss))
        new_aliases |= aliases_to_add
        new_aliases -= aliases_to_remove

    return new_aliases


async def do_edit_boss(
    state: State,
    boss: str,
    new_name: str | None,
    new_aliases: set[str],
    aliases_to_add: set[str],
    aliases_to_remove: set[str]
) -> str:
    new_aliases_or_msg = _new_aliases(
        state, boss, new_name, new_aliases, aliases_to_add, aliases_to_remove
    )
    if isinstance(new_aliases_or_msg, str):
        return new_aliases_or_msg
    new_aliases = new_aliases_or_msg
    new_name = new_name or boss

    state.update_boss(boss, new_name, new_aliases)
    return f'Successfully applied edits: {state.boss_info(new_name)}'


async def do_edit_spawn(
    state: State,
    spawn: tuple[str, str],
    new_name: str | None,
    new_map: str | None,
    new_min: int | None,
    new_max: int | None,
    new_aliases: set[str],
    aliases_to_add: set[str],
    aliases_to_remove: set[str]
) -> str:
    boss, loc = spawn
    spawn = state.spawns(boss)[loc]
    new_map = new_map or loc
    new_min = new_min or spawn['min']
    new_max = new_max or spawn['max']
    new_aliases_or_msg = _new_aliases(
        state, boss, new_name, new_aliases, aliases_to_add, aliases_to_remove
    )
    if isinstance(new_aliases_or_msg, str):
        return new_aliases_or_msg
    new_aliases = new_aliases_or_msg

    new_name = new_name or boss

    if new_min > new_max:
        return _fail(
            'Failed to edit',
            'min respawn time is greater than max respawn time'
        )

    if loc != new_map and new_map in state.spawns(boss):
        return _fail(
            'Failed to edit',
            f'{loc} is already a name of a spawn for {boss}'
        )

    state.update_spawn(
        boss, loc, new_name, new_map, new_min, new_max, new_aliases
    )
    return f'Successfully applied edits: {state.boss_info(new_name)}'


async def handle_expire(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to set expire time', reason)

    if not args:
        return f'Expiration time is {state.expire_time_str}'

    if len(args) > 1:
        return fail('expected at most 1 argument')
    minutes = parse_time(args[0])
    if minutes is None:
        return fail(
            'tracked boss expiration time should be in HH:MM format, or just '
            'the number of minutes'
        )

    if minutes < 0:
        return fail('expire time must be not be negative')
    state.expire_time = minutes
    if minutes:
        return (
            f'Tracked monster expiration time now set to '
            f'{state.expire_time_str}'
        )
    else:
        return (
            f'Tracked monster expiration time is now unset: monsters will '
            f'remain tracked until they are either tracked again with !t or '
            f'!tracked or they are cancelled with !track-cancel.'
        )


async def handle_remove(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to remove boss', reason)

    if not args:
        return fail('no boss given')

    if len(args) > 1:
        return fail('expected exactly one argument')

    name = args[0]
    bosses = state.resolve(name)
    if not bosses:
        return fail(f'{name} is not a recognized boss or alias')
    if state.unambiguous(bosses):
        return await do_remove(state, state.first_spawn(bosses))

    return state.disambiguation_prompt(
        'Which spawn to remove?',
        state.spawn_options(bosses),
        do_remove
    )


async def do_remove(state: State, spawn: tuple[str, str]) -> str:
    boss, loc = spawn
    label = state.boss_label(boss, loc)
    if state.remove(boss, loc):
        await state.refresh()
    return f'{label} is no longer trackable.'


async def handle_remove_alert(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to remove alert', reason)

    if args:
        return fail('!t-remove-alert expects 0 arguments')

    if not state.alerts:
        return fail('No alerts to remove')

    if len(state.alerts) == 1:
        return await do_remove_alert(state, 0)

    return state.disambiguation_prompt(
        'Which alert do you want to remove?',
        list(zip(state.alerts, tuple(range(len(state.alerts))))),
        do_remove_alert,
        sort=False
    )


async def do_remove_alert(state: State, i: int) -> str:
    removed = state.alerts[i]
    state.remove_alert(i)
    return f'Successfully removed alert: {removed}'


async def handle_remove_editor(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to remove editor', reason)

    if not args:
        return fail('no user mentions given')

    components = []
    for arg in args:
        mem_id = parse_user_mention(arg)
        if not mem_id:
            components.append(fail(f'{arg} is not a user mention'))
        elif not state.is_editor(mem_id):
            components.append(fail(f'{arg} is not an editor'))
        else:
            try:
                state.config['editors'].remove(mem_id)
                components.append(f'Removed {arg} as an editor')
            except ValueError:
                components.append(
                    fail(f'{arg} is a server manager and may not be removed')
                )
    return '\n'.join(components)


async def handle_track(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to track boss', reason)

    if 'channel' not in state.config:
        return fail(
            'Tracking channel not configured. Use !track-channel to set the '
            'tracking channel.'
        )

    if not args:
        await state.refresh()
        return 'Tracking info refreshed'

    args, disamb_idxs = State.extract_disamb_range(args)
    tod = None
    window = 0
    name_end = len(args)
    try:
        q_index = args.index('?')
    except ValueError:
        if len(args) > 1:
            tod = state.parse_time(args[-1])
            if tod is not None:
                name_end -= 1
                if len(args) > 2:
                    alive_time = state.parse_time(args[-2])
                    if alive_time is not None:
                        if tod >= alive_time:
                            return fail(
                                'Alive time should be before death time'
                            )
                        name_end -= 1
                        window = alive_time - tod
    else:
        window = None
        name_end = q_index
        extra = len(args) - q_index - 1
        if extra > 1:
            return fail('only 1 argument expected after question mark')
        if extra == 1:
            tod = state.parse_time(args[-1])
            if tod is None:
                return fail(f'{args[-1]} is not a valid time')

    name = ' '.join(args[:name_end])

    bosses = state.resolve(name)
    if not bosses:
        return fail(f'{name} is not a recognized boss or alias')

    tod = tod or state.send_time

    if state.unambiguous(bosses):
        if disamb_idxs:
            return fail(f'{name} is already unambiguous')
        return await do_track(
            state, state.first_spawn(bosses), tod, window, True
        )

    options = state.spawn_options(bosses)
    if disamb_idxs:
        if disamb_idxs[-1] > len(options):
            return fail(
                f'{disamb_idxs[-1]} greater than number of options to choose '
                f'from'
            )
        multi_options = [options[i - 1][1] for i in disamb_idxs]
        return await do_track_multi(state, multi_options, tod, window)
    return state.disambiguation_prompt(
        'Which spawn was it?', options, do_track, (tod, window, True)
    )


async def do_track(
    state: State,
    spawn: tuple[str, str],
    tod: float,
    window: float | None,
    refresh_now: bool
) -> str:
    boss, loc = spawn
    max_spawn = state.max(boss, loc)
    if window is None:
        if (boss, loc) in state.tracked:
            old_tod = state.tod(boss, loc)
            if tod > old_tod:
                min_time, _, _ = state.spawn_info(boss, loc)
                window = min(tod - min_time, max_spawn)
            else:
                # Assume intention is overwrite in this case.
                window = max_spawn
        else:
            window = max_spawn
    if window > state.max(boss, loc):
        return _fail(
            'Failed to track boss',
            f'a time of death window longer than the max spawn time '
                f'({max_spawn} minutes) is not supported.'
        )
    state.track(boss, loc, tod, window)
    if window:
        die_msg = (
            f'died between {state.format_time(tod - window)} and '
            f'{state.format_time(tod)}'
        )
    else:
        die_msg = f'died at {state.format_time(tod)}'
    if refresh_now:
        await state.refresh()
    return f'Now tracking {state.boss_label(boss, loc)} ({die_msg})'


async def do_track_multi(
    state: State,
    spawns: list[tuple[str, str]],
    tod: float,
    window: float | None
) -> str:
    components = []
    for spawn in spawns:
        components.append(await do_track(state, spawn, tod, window, False))
    await state.refresh()
    return '\n'.join(components)


# noinspection PyUnusedLocal
async def handle_track_help(state: State, args: list[str]) -> str:
    preamble = 'Note: arguments ignored\n\n' if args else ''
    return f'```\n{preamble}{HELP_MSG}\n```'


async def handle_utc_offset(state: State, args: list[str]) -> str:
    def fail(reason: str) -> str:
        return _fail('Failed to set UTC offset', reason)

    if not args:
        return f'Server time UTC offset: {state.utc_offset_str}'

    if len(args) > 1:
        return fail('expected at most one argument')

    minutes = parse_time(args[0])

    if ':' not in args[0] or abs(minutes) >= 24 * 60:
        return fail(f'{args[0]} not formatted as HH:MM or -HH:MM')

    state.utc_offset = minutes
    return f'Server time UTC offset set to {state.utc_offset_str}'


CMD_TO_FN = {
    'track': handle_track,
    'track-add': handle_add,
    'track-add-editor': handle_add_editor,
    'track-alert': handle_alert,
    'track-alert-role': handle_alert_role,
    'track-auto-refresh': handle_auto_refresh,
    'track-cancel': handle_cancel,
    'track-channel': handle_channel,
    'track-conf': handle_conf,
    'track-edit': handle_edit,
    'track-expire': handle_expire,
    'track-help': handle_track_help,
    'track-remove': handle_remove,
    'track-remove-alert': handle_remove_alert,
    'track-remove-editor': handle_remove_editor,
    'track-utc-offset': handle_utc_offset
}

NEEDS_EDITOR = {
    handle_add,
    handle_add_editor,
    handle_alert,
    handle_alert_role,
    handle_auto_refresh,
    handle_channel,
    handle_edit,
    handle_expire,
    handle_remove,
    handle_remove_alert,
    handle_remove_editor,
    handle_utc_offset
}


def main() -> None:
    global global_config
    if not os.path.exists(CONF):
        with open(CONF, 'w') as f:
            json.dump({}, f)
    with open(CONF, 'r') as f:
        global_config = json.load(f)

    for guild, config in global_config.items():
        load_state(guild, State(config), False)

    client.run(os.environ['DISCORD_TOKEN'])


if __name__ == '__main__':
    main()
