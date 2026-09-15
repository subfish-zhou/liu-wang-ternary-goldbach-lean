#!/usr/bin/env python3
"""Single supported entry point; bounded parallelism with per-module locks."""
from closure_scheduler import main

if __name__ == '__main__':
    raise SystemExit(main())
