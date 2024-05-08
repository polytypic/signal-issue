# Steps to reproduce

```sh
while dune exec -- ./signal_issue.exe ; do echo; done
```

The above will sooner or later stop, possibly without error message, as
the program is terminated by a SIGSEGV or SIGBUS.
