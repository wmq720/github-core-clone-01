# forge

A standalone GitHub-compatible git forge in a single static Go binary.

- git smart HTTP: upload-pack v2 (ls-refs, fetch, shallow) + receive-pack v0
- REST v3 (`/api/v3`), GraphQL v4 (`/api/graphql`), MCP (`/mcp`)
- hand-written raw-TCP HTTP/1.1 server, keep-alive, zero-allocation hot paths

Build: `CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -o forge forge.go`
Run: `node main.ts` (spawns `./forge`, which binds, registers with
`$MAKEFUN_ENV_URL`, serves until `/done`, then exits 0).
