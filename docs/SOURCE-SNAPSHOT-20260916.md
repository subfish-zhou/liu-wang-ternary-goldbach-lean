# Source-only WIP checkpoint / 源码保全检查点

This snapshot preserves uncommitted Lean source, including generated finite certificates,
partial proofs and historical probes. It is **not** a verified theorem release.
Some files have matching local compile/replay records; others remain uncompiled or failed.
The accepted entry point and mathematical admission checkpoint are not extended by this snapshot.

本次按用户要求先上传源码保全，不等待全量构建。包含未完成、未核收和可能编译失败的草稿，
不能把源码进入 main 解释成已证明三素数定理。实际主根仍含 M04（有限高度零点完整性）
与 M06（原全整数 totient 界）。未改 Accepted.lean 或正式数学准入清单。

Captured additions: 1399 Lean files, 820877229 bytes. Of these, 710 match a checked
local source/object record at capture time; this is not independent parent acceptance.
Per-file hashes and status are in `verification/source-snapshot-20260916.json`.
Active writers were not stopped; their subsequent edits are not part of the captured bytes.

Excluded: `.lake` caches and private logs, CLI sessions, credentials, AGENTS changes,
and unreviewed launcher/scheduler edits. No whole-project build was run for this preservation push.
