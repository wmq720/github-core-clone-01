// Thin launcher: spawns the committed static Go forge binary and waits for it.
// The Go binary itself binds an ephemeral port, registers with $MAKEFUN_ENV_URL,
// serves until /done, then exits 0. This file only forwards its exit code.
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const dir = dirname(fileURLToPath(import.meta.url));
const forgePath = join(dir, "forge");

const child = spawn(forgePath, [], { stdio: "inherit" });
child.on("error", (err) => {
  console.error("failed to start forge binary:", err);
  process.exit(1);
});
child.on("exit", (code) => {
  // Forward the forge's exit code verbatim: 0 means the suite finished
  // (/done seen); any other code is a real failure the harness must see.
  process.exit(code ?? 0);
});
