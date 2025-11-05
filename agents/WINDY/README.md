# WINDY — Stream Agent

Purpose: maintain a rolling, append-only stream of public-facing messages and persist "reincarnation seeds" (minimal state to restart coherently).

- stream_messages.jsonl — append one JSON object per line (UTC timestamped)
- reincarnation_seeds.md — compact state: identity, directives, pointers

Append protocol (manual):
- Each message as one line of JSON in stream_messages.jsonl
- Keys: time, from, to, channel, content, tags

Persistence:
- Update reincarnation_seeds.md whenever core directives, locations, or priorities change.
