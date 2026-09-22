#!/usr/bin/env python3
"""Check stitched argument specializations and their runtime tag fallbacks.

Usage: python3 test-support/jit-region-arguments.py DATABASE [MOO]
Uses a disposable server so region specialization runs at scheduler boundaries.
"""

import json
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import socket
import time


cases = [
    ("identity", "{x, n} = args; return x;", "{1, 2}",
     '{{1,2},{1.5,2},{#1,2},{"text",2},{{1,2},2}}'),
    ("numeric guard", "{x, n} = args; return x + n;", "{1, 2}",
     '{{1,2},{1.5,2.5},{"a","b"},{{1},{2}},{#1,2}}'),
    ("shift and exact exit", "{x, n} = args; return x << n;", "{1, 2}",
     '{{1,2},{-5,3},{0,63},{1,64},{1,-1},{1.5,2},{"x",1},{#1,1}}'),
    ("list argument", "{xs,n}=args; r=0; for x in (xs) r=r+x; endfor return r;",
     '{{1,2,3},0}', '{{{1,2,3},0},{{},0},{{4,5},0},{{1,"x"},0},{42,0}}'),
    ("signed remainder", "{x,n}=args; return x % 4294967296;", '{9,0}',
     '{{9,0},{-9,0},{4294967297,0},{-4294967297,0},{-9223372036854775808,0}}'),
    ("virtual slice", "{xs,n}=args; s=xs[n..n+1]; return s[1]*256+s[2];",
     '{{1,2,3},1}', '{{{1,2,3},1},{{1,2,3},2},{{1},1},{{1,2},0},{{1,"x"},1}}'),
    ("empty slice", "{xs,n}=args; s=xs[n..0]; return length(s);",
     '{{1,2,3},1}', '{{{1,2,3},1},{{},1},{{1,2},7},{{1,2},-1}}'),
]

lines = [
    ';add_verb(#0,{player,"rxd","__region_arg_leaf"},{"this","none","this"})',
    ';add_verb(#0,{player,"rxd","__region_arg_caller"},{"this","none","this"})',
]
for label, source, warm, inputs in cases:
    lines += [
        ';set_verb_code(#0,"__region_arg_leaf",{' + json.dumps(source) + '})',
        ';set_verb_code(#0,"__region_arg_caller",'
        '{"return this:__region_arg_leaf(args[1], args[2]);"})',
        ';;expected={}; for a in (' + inputs + ') '
        'try r={1,#0:__region_arg_caller(@a)}; except e (ANY) r={0,e[1]}; endtry '
        'expected={@expected,r}; endfor #0.__region_arg_expected=expected; return 1;',
        ';jit_compile(#0,"__region_arg_leaf")',
        ';jit_compile(#0,"__region_arg_caller")',
        ';;for i in [1..40] r=#0:__region_arg_caller(@' + warm + '); endfor return 1;',
        ';jit_pool_rotate()',
        ';jit_compile(#0,"__region_arg_caller")',
        ';;d=disassemble(#0,"__region_arg_caller","hir"); spliced=0; '
        'for x in (d) if (index(x,"spliced=1")) spliced=1; endif endfor '
        'if (!spliced) return {"FAIL","not stitched",' + json.dumps(label) +
        ',disassemble(#0,"__region_arg_leaf","hir")}; endif '
        'i=0; for a in (' + inputs + ') i=i+1; '
        'try r={1,#0:__region_arg_caller(@a)}; except e (ANY) r={0,e[1]}; endtry '
        'if (!equal(r,#0.__region_arg_expected[i])) return '
        '{"FAIL",' + json.dumps(label) + ',a,r,#0.__region_arg_expected[i]}; endif '
        'endfor return {"PASS",' + json.dumps(label) + '};',
    ]
lines.insert(2, ';add_property(#0,"__region_arg_expected",{},{player,"rw"})')
lines += [
    ';add_property(#0,"__region_arg_receiver",#1,{player,"rw"})',
    ';add_property(#1,"__region_arg_bias",1,{player,"rw"})',
    ';;#0.__region_arg_bias=9; return 1;',
    ';add_verb(#1,{player,"rxd","__region_remote"},{"this","none","this"})',
    ';set_verb_code(#1,"__region_remote",'
    '{"return args[1] / args[2] + this.__region_arg_bias;"})',
    ';set_verb_code(#0,"__region_arg_leaf",'
    '{"target = this.__region_arg_receiver; return target:__region_remote(args[1],args[2]);"})',
    ';set_verb_code(#0,"__region_arg_caller",'
    '{"return this:__region_arg_leaf(args[1],args[2]);"})',
    ';jit_compile(#1,"__region_remote")',
    ';jit_compile(#0,"__region_arg_leaf")',
    ';jit_compile(#0,"__region_arg_caller")',
    ';;for i in [1..80] r=#0:__region_arg_caller(42,2); endfor return 1;',
    ';jit_pool_rotate()',
    ';;for i in [1..40] r=#0:__region_arg_caller(42,2); endfor return 1;',
    ';jit_pool_rotate()',
    ';;r=#0:__region_arg_caller(42,2); d=disassemble(#0,"__region_arg_caller","hir"); '
    'spliced=0; for x in (d) if (index(x,"spliced=1")) spliced=1; endif endfor '
    'if (!spliced || r!=22) return {"FAIL","object receiver",r,d}; endif '
    'try r=#0:__region_arg_caller(42,0); return {"FAIL","missing divide error"}; '
    'except(E_DIV) endtry return {"PASS","object receiver and exact exit"};',
    ';;#0.__region_arg_receiver=#0; r=#0:__region_arg_caller(42,2); '
    'if (r!=30) return {"FAIL","stale receiver",r}; endif '
    'return {"PASS","changed receiver"};',
]
lines += [
    ';;for i in [1..40] r=#430:hash(""); endfor return 1;',
    ';jit_pool_rotate()',
    ';;for i in [1..40] r=#430:hash(""); endfor return 1;',
    ';jit_pool_rotate()',
    ';;#430:hash(""); return 1;',
    ';;before=disassemble(#430,"raw_hash","hir"); spliced=0; '
    'for x in (before) if (index(x,"spliced=1")) spliced=1; endif endfor '
    'if (!spliced) return {"FAIL","MIR dump needs stitched regions"}; endif '
    'for i in [1..3] d=disassemble(#430,"raw_hash","mir"); '
    'if (!length(d) || !equal(before,disassemble(#430,"raw_hash","hir"))) '
    'return {"FAIL","MIR dump changed installed metadata"}; endif endfor '
    'return {"PASS","read-only stitched MIR dump"};',
    ';;#430:hash(""); return {"PASS","execution after MIR dump"};',
]
for message in ["", "abc", "a" * 55, "a" * 56, "a" * 64, "a" * 1000]:
    expected = hashlib.sha256(message.encode()).hexdigest()
    lines.append(';;r=#430:hash(' + json.dumps(message) + '); '
                 'if (r!=' + json.dumps(expected) + ') return {"FAIL","SHA-256",r}; '
                 'endif return {"PASS","SHA-256"};')
with tempfile.TemporaryDirectory(prefix="moo-region-arguments-") as directory:
    temp = Path(directory)
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        port = probe.getsockname()[1]
    server = subprocess.Popen(
        [sys.argv[2] if len(sys.argv) > 2 else "./moo", "-l",
         str(temp / "server.log"), sys.argv[1], str(temp / "output.db"),
         "-p", str(port)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    sock = None
    line = "server startup"
    output = ""
    try:
        deadline = time.monotonic() + 90
        while sock is None:
            if server.poll() is not None:
                raise RuntimeError("server exited during startup")
            try:
                sock = socket.create_connection(("127.0.0.1", port), timeout=1)
            except OSError:
                if time.monotonic() > deadline:
                    raise
                time.sleep(0.5)
        sock.settimeout(120)
        sock.sendall(b"connect wizard homerhead\n")
        for line in lines:
            sock.sendall((line + "\n").encode())
            response = b""
            while b"\xe2\x87\x92" not in response or not response.endswith(b"\n"):
                chunk = sock.recv(65536)
                if not chunk:
                    raise RuntimeError("server closed connection")
                response += chunk
                if b"(End of traceback)" in response:
                    raise RuntimeError(response.decode(errors="replace"))
            output += response.decode(errors="replace")
    except Exception:
        print("Failed command:", line)
        print((temp / "server.log").read_text())
        raise
    finally:
        if sock:
            try:
                sock.sendall(b';;shutdown("region argument tests complete");\n')
                sock.close()
            except OSError:
                pass
        try:
            server.wait(timeout=30)
        except subprocess.TimeoutExpired:
            server.terminate()
            server.wait(timeout=30)
    if '"FAIL"' in output or output.count('{"PASS",') != len(cases) + 10:
        print(output)
        print((temp / "server.log").read_text())
        raise SystemExit(1)
    print(f"PASS: {len(cases) + 2} stitched argument/receiver/fallback cases, "
          "repeated MIR dumps, 6 SHA-256 vectors")
