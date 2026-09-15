#!/usr/bin/env python3
"""Single supported entry point; bounded parallelism with per-module locks."""
from closure_scheduler import main

if __name__ == '__main__':
    from pathlib import Path
    import sys
    from project_dependency_guard import enforce_worker_imports
    enforce_worker_imports(Path(__file__).resolve().parents[1], sys.argv[1:])
    raise SystemExit(main())
