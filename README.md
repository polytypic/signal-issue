# Steps to reproduce

```sh
while                                       \
  if dune exec -- ./signal_issue.exe; then  \
    echo OK;                                \
  else                                      \
    echo "ERROR: $?";                       \
    return 1;                               \
  fi;                                       \
do                                          \
  echo;                                     \
done
```

The above will sooner or later stop and the last line will read `ERROR: 138` or
`ERROR: 139` indicating a `SIGBUS` or `SIGSEGV`.

Running the program under `lldb` on macOS with e.g.

```sh
lldb                                        \
  --file ./_build/default/signal_issue.exe  \
  -o 'pro hand -p true -s false SIGUSR2'    \
  -o run
```

and you get lucky, the program stops at either

```
* thread #1, queue = 'com.apple.main-thread', stop reason = EXC_BAD_ACCESS (code=1, address=0x8)
    frame #0: 0x00000001000b6e10 signal_issue.exe`caml_runstack + 108
signal_issue.exe`caml_runstack:
->  0x1000b6e10 <+108>: ldr    x26, [x16, #0x8]
    0x1000b6e14 <+112>: str    x26, [x28, #0x30]
    0x1000b6e18 <+116>: ldr    x21, [x16]
    0x1000b6e1c <+120>: ldr    x16, [x28, #0x40]
```

or

```
* thread #1, queue = 'com.apple.main-thread', stop reason = EXC_BAD_ACCESS (code=1, address=0x128100000)
    frame #0: 0x000000018723b200 libsystem_platform.dylib`_platform_memmove + 96
libsystem_platform.dylib`:
->  0x18723b200 <+96>:  ldnp   q0, q1, [x1]
    0x18723b204 <+100>: add    x1, x1, #0x20
    0x18723b208 <+104>: subs   x2, x2, #0x20
    0x18723b20c <+108>: b.hi   0x18723b1f8               ; <+88>
```

The program in this repository is a stripped down version of the test program
[test_server_and_client](https://github.com/ocaml-multicore/picos/blob/234256f2a4f8f3ce3c7ffc96ff4ac3e474393e1a/test/test_server_and_client.ml#L1-L133)
in Picos. Signals are used to force a blocking system call to return. The
stripped down version of the program here is modified to remove all uses of
"unsafe" OCaml features (which are evidently not the cause of this issue).

The problem has also been reproduced by Edwin Török:

> I tried 5.1.1 on aarch64 (my Android phone, using UserLand and
> `opam init --disable-sandboxing`). It does reproduce the problem (well the
> program just exits).

So, this does not seem to be an OS-specific issue.
