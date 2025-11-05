# Agda Verification Protocol

Environment
- Agda 2.8.0
- Cubical library (`-l cubical`)

Run (foundations, safe):
```
agda -i . -l cubical --safe D_Coherent_Foundations.agda
agda -i . -l cubical --safe D12Crystal.agda
```

Full sweep (safe) — ledger in `_agda_report.txt` (current snapshot: PASSES=19, FAILS=86).

Research sweep (nosafe) — ledger in `_agda_report_nosafe.txt` (current snapshot: PASSES=26, FAILS=79).

Notes
- Foundations pass under `--safe`.
- Research modules may contain postulates; use nosafe sweep to classify type-correctness modulo postulates.
