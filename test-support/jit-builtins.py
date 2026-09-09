#!/usr/bin/env python3
"""Compare interpreted and native builtin calls using a disposable database.

Usage: python3 test-support/jit-builtins.py DATABASE [--moo ./moo]
The database must load in the current server. These tests do not suspend;
emergency mode exits with `abort`, so the input database is never saved.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

cases = []


def add(name, expression, arguments):
    cases.append((name, expression, arguments))


for name in ('tonum', 'toint', 'tofloat', 'toobj'):
    for value in ('42', '#42', 'E_INVARG', '-3.75', '"42"',
                  '"127.0.0.1"', '{}', '1.0e100'):
        add(name + ' ' + value, f'{name}(args[1])', '{' + value + '}')
for name in ('min', 'max'):
    for arguments in ('{4,-2}', '{4.5,-2.5}', '{4,2,-3,9}',
                      '{4.5,2.5,-3.5,9.5}', '{4,2.5}', '{4.5,2}'):
        operands = ','.join(f'args[{i + 1}]'
                            for i in range(arguments.count(',') + 1))
        add(name + ' ' + arguments, f'{name}({operands})', arguments)
for case in [
    ('equal case', 'equal(args[1],args[2])', '{"a","A"}'),
    ('equal lists', 'equal(args[1],args[2])', '{{"x",{1}},{"x",{1}}}'),
    ('strcmp', 'strcmp(args[1],args[2])', '{"a","A"}'),
    ('strcmp type', 'strcmp(args[1],args[2])', '{1,"A"}'),
    ('ord', 'ord(args[1])', '{"A"}'),
    ('ord unicode', 'ord(args[1])', '{"é"}'),
    ('ord empty', 'ord(args[1])', '{""}'),
    ('ord long', 'ord(args[1])', '{"ab"}'),
    ('tochar', 'tochar(args[1])', '{65}'),
    ('tochar unicode', 'tochar(args[1])', '{233}'),
    ('tochar string', 'tochar(args[1])', '{"A"}'),
    ('tochar invalid', 'tochar(args[1])', '{-1}'),
    ('tostr', 'tostr(@args)', '{42,#42,1.5,"text",{1,2},E_INVARG}'),
    ('tostr empty', 'tostr()', '{}'),
    ('strsub', 'strsub(args[1],args[2],args[3])', '{"aAa","a","xyz"}'),
    ('strsub case', 'strsub(args[1],args[2],args[3],args[4])',
     '{"aAa","a","xyz",1}'),
    ('strsub empty', 'strsub(args[1],args[2],args[3])', '{"abc","","x"}'),
    ('listset', 'listset(args[1],args[2],args[3])', '{{1,"old",{3}},{"new"},2}'),
    ('listset invalid', 'listset(args[1],args[2],args[3])', '{{1},2,5}'),
]:
    add(*case)
for name in ('listappend', 'listinsert'):
    for arguments, operands in [
        ('{{1,2},"x"}', 'args[1],args[2]'),
        ('{{},1.5}', 'args[1],args[2]'),
        ('{{1,2},{"x"},-9}', 'args[1],args[2],args[3]'),
        ('{{1,2},"x",99}', 'args[1],args[2],args[3]'),
    ]:
        add(name + arguments, f'{name}({operands})', arguments)
for name in ('sqrt', 'floor', 'ceil', 'trunc'):
    for value in ('2.75', '-2.75', '0.0', '2'):
        add(name + value, f'{name}(args[1])', '{' + value + '}')
# Keep the original list live across the call to test copy-on-write.
for name in ('listappend', 'listinsert', 'listset'):
    add(name + ' alias', '{' + name + '(args[1],args[2],2),args[1]}',
        '{{1,2,3},{"new"}}')

# Known types exercise the unboxed register paths as well as tagged arguments.
for expression in ('tonum("42")', 'toint(-3.75)', 'toint(#42)',
                   'min(3.5, -2.5)', 'max(-2.5, 3.5)',
                   'min(1, 2, 3)', 'max(1.5, 2.5, 3.5)',
                   'tostr(min(-0.0, 0.0))', 'tostr(max(0.0, -0.0))',
                   'sqrt(4.0)', 'floor(-2.75)', 'ceil(-2.75)', 'trunc(-2.75)'):
    add(expression, expression, '{}')
for name in ('tonum', 'toint', 'tofloat', 'toobj', 'equal', 'strcmp',
             'listappend', 'listinsert', 'listset', 'ord', 'tochar',
             'sqrt', 'floor', 'ceil', 'trunc', 'min', 'max', 'strsub'):
    add(name + ' wrong arity', name + '(@args)', '{}')
add('nested owned calls', 'tostr(strsub(tochar(args[1]), "A", "xyz"), args[2])',
    '{65, "suffix"}')
add('owned result before error', '{listappend(args[1], 4), sqrt(args[2])}',
    '{{1,2,3}, -1.0}')

add('string results across loop iterations', [
    'value = args[1];',
    'for i in [1..40]',
    '  value = strsub(value,"a","b");',
    '  value = strsub(value,"b","a");',
    'endfor',
    'return {value,args[1]};',
], '{"aaaa"}')
add('list results across loop iterations', [
    'value = args[1];',
    'for i in [1..40]',
    '  value = listappend(value,i);',
    '  value = listset(value,tochar(65),1);',
    'endfor',
    'return {value,args[1]};',
], '{{1,2}}')


def moo_string(value):
    return json.dumps(value, ensure_ascii=False)


def comparison(index, expression, arguments):
    label = moo_string(cases[index][0])
    source = expression if isinstance(expression, list) else ['return ' + expression + ';']
    code = '{' + ','.join(moo_string(line) for line in source) + '}'
    return [
        ';set_verb_code(#0,"__jit_builtin_probe",' + code + ')',
        f';;a={arguments}; '
        'try expected={1,#0:__jit_builtin_probe(@a)}; '
        'except e (ANY) expected={0,e[1]}; endtry '
        'm=jit_compile(#0,"__jit_builtin_probe"); '
        'for i in [1..10] '
        'try actual={1,#0:__jit_builtin_probe(@a)}; '
        'except e (ANY) actual={0,e[1]}; endtry '
        f'if (!equal(actual,expected)) return {{"FAIL",{label},expected,actual}}; '
        'endif endfor m=jit_compile(#0,"__jit_builtin_probe"); '
        f'return {{"CASE",{index},expected[1],m[1][2],m[10][2],m[11][2],'
        'm[12][2],m[13][2]};'
    ]


def set_option(name, value):
    return (f';;try add_property($server_options,"{name}",{value},'
            f'{{player,"rw"}}); except(E_INVARG) '
            f'$server_options.{name}={value}; endtry '
            'load_server_options(); return 1;')


def protection_checks():
    expressions = {
        'tonum': 'tonum(args[1])', 'toint': 'toint(args[1])',
        'tofloat': 'tofloat(args[1])', 'toobj': 'toobj(args[1])',
        'min': 'min(args[1],args[1])', 'max': 'max(args[1],args[1])',
        'equal': 'equal(args[1],args[1])', 'strcmp': 'strcmp("a","a")',
        'listappend': 'listappend({},args[1])',
        'listinsert': 'listinsert({},args[1])',
        'listset': 'listset({1},args[1],1)', 'ord': 'ord("A")',
        'tochar': 'tochar(args[1])', 'sqrt': 'sqrt(4.0)',
        'floor': 'floor(4.0)', 'ceil': 'ceil(4.0)', 'trunc': 'trunc(4.0)',
        'tostr': 'tostr(args[1])', 'strsub': 'strsub("abc","b","x")',
    }
    lines = [';add_verb(player,{player,"rxd","__jit_builtin_protection"},'
             '{"this","none","this"})']
    for name, expression in expressions.items():
        lines.extend([
            ';set_verb_code(player,"__jit_builtin_protection",{' +
            moo_string('return {' + expression + '};') + '})',
            ';jit_compile(player,"__jit_builtin_protection")',
            ';player:__jit_builtin_protection(65)',
            f';;try delete_verb(#0,"bf_{name}"); except(E_VERBNF) endtry '
            f'return add_verb(#0,{{player,"rxd","bf_{name}"}},'
            '{"this","none","this"});',
            f';set_verb_code(#0,"bf_{name}",{{' +
            moo_string('return "PROTECTED";') + '})',
            set_option('protect_' + name, 1),
            ';;for i in [1..3] if (!equal(player:__jit_builtin_protection(65), '
            f'{{"PROTECTED"}})) return {{"FAIL","protection {name}"}}; '
            f'endif endfor return {{"PROTECTED","{name}"}};',
            set_option('protect_' + name, 0),
        ])
    return lines, len(expressions)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('database', type=Path)
    parser.add_argument('--moo', type=Path, default=Path('./moo'))
    parser.add_argument('--artifacts', type=Path)
    options = parser.parse_args()
    lines = [';jit_profile_detail(1)',
             ';add_verb(#0,{player,"rxd","__jit_builtin_probe"},'
             '{"this","none","this"})']
    for index, (_, expression, arguments) in enumerate(cases):
        lines.extend(comparison(index, expression, arguments))
    protected, protection_count = protection_checks()
    lines.extend(protected)
    # Quota failures must reach the canonical catchable E_QUOTA path.
    lines.extend([set_option('max_string_concat', 1024),
                  set_option('max_list_concat', 1024),
                  set_option('max_concat_catchable', 1)])
    quota_cases = [
        ('tostr', 'tostr(args[1],args[1])', '{' + moo_string('x' * 768) + '}'),
        ('strsub', 'strsub(args[1],"x","xx")', '{' + moo_string('x' * 768) + '}'),
        ('listappend', 'listappend(args[1],2)', '{{' + ','.join(['1'] * 1024) + '}}'),
        ('listinsert', 'listinsert(args[1],2)', '{{' + ','.join(['1'] * 1024) + '}}'),
    ]
    for name, expression, arguments in quota_cases:
        lines.extend([
            ';set_verb_code(#0,"__jit_builtin_probe",{' +
            moo_string('return ' + expression + ';') + '})',
            ';jit_compile(#0,"__jit_builtin_probe")',
            f';;a={arguments}; try #0:__jit_builtin_probe(@a); '
            f'return {{"FAIL","quota {name}"}}; '
            f'except(E_QUOTA) return {{"QUOTA","{name}"}}; endtry',
        ])
    lines.extend([
        set_option('max_concat_catchable', 0),
        ';set_verb_code(#0,"__jit_builtin_probe",{' +
        moo_string('return tostr(args[1],args[1]);') + '})',
        ';jit_compile(#0,"__jit_builtin_probe")',
        ';"UNCATCHABLE START"',
        ';;try #0:__jit_builtin_probe(' + moo_string('x' * 768) + '); '
        'return "FAIL: quota did not abort"; except(ANY) '
        'return "FAIL: abort was catchable"; endtry',
        ';"UNCATCHABLE END"',
        ';"BUILTINS DONE"', 'abort',
    ])
    with tempfile.TemporaryDirectory(prefix='moo-jit-builtins-') as tmp:
        work = options.artifacts or Path(tmp)
        work.mkdir(parents=True, exist_ok=True)
        source = '\n'.join(lines) + '\n'
        (work / 'input.moo').write_text(source)
        proc = subprocess.run(
            [str(options.moo.resolve()), '-e', '-l', str(work / 'server.log'),
             str(options.database.resolve()), str(work / 'output.db')],
            input=source, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=120)
        (work / 'output.txt').write_text(proc.stdout)
        reports = re.findall(
            r'=> {"CASE", (\d+), ([01]), "([^"]+)", (\d+), (\d+), (\d+), (\d+)}',
            proc.stdout)
        failures = []
        if proc.returncode != 1 or '=> "BUILTINS DONE"' not in proc.stdout:
            failures.append('server did not finish the comparisons')
        if len(reports) != len(cases):
            failures.append(f'expected {len(cases)} reports, got {len(reports)}')
        if len(re.findall(r'=> {"PROTECTED",', proc.stdout)) != protection_count:
            failures.append('protected builtin override checks failed')
        if len(re.findall(r'=> {"QUOTA",', proc.stdout)) != len(quota_cases):
            failures.append('catchable quota checks failed')
        abort_output = proc.stdout.split('=> "UNCATCHABLE START"')[-1].split(
            '=> "UNCATCHABLE END"')[0]
        if '*Aborted*' not in abort_output or 'FAIL:' in abort_output:
            failures.append('uncatchable quota did not abort the task')
        direct = 0
        for index, success, state, entries, completed, vm_calls, deopts in reports:
            name = cases[int(index)][0]
            if state != 'compiled' or int(entries) < 10:
                failures.append(f'{name}: native code was not exercised')
            if success == '1':
                direct += 1
                if (int(completed), int(vm_calls), int(deopts)) != (10, 0, 0):
                    failures.append(f'{name}: successful call used fallback '
                                    f'(completed={completed}, vm={vm_calls}, deopts={deopts})')
        if failures:
            print(proc.stdout)
            log = work / 'server.log'
            if log.exists():
                print(log.read_text(errors='replace')[-4000:])
            raise SystemExit('\n'.join(failures))
        print(f'{len(cases)} builtin comparisons passed; '
              f'{direct} successful cases completed natively without VM calls or deopts. '
              f'{protection_count} protection, {len(quota_cases)} catchable quota, '
              'and one uncatchable quota check passed.')


if __name__ == '__main__':
    main()
