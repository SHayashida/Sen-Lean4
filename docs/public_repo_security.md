# Public Repository Security Notes

## AGENTS policy
- Keep `AGENTS.md` public-safe: no secrets, tokens, private keys, internal URLs, or local absolute paths.
- Put private machine/user instructions in `AGENTS.local.md` (git-ignored), not in committed docs.

## CI secret handling
- Do not expose repository secrets to untrusted pull requests.
- Prefer running untrusted PR jobs without secrets and without write-scoped credentials.
- Keep workflow steps deterministic and avoid printing secret-bearing environment variables.

## Least-privilege `GITHUB_TOKEN`
- Use minimum required permissions per workflow/job.
- Default to read-only permissions unless a job truly needs write access.

## Scanning and push protection
- Enable secret scanning / push protection when available.
- Treat any detected credential pattern as an immediate rotation-and-rewrite incident.
