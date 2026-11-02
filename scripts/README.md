# Scripts for working on cslib

This directory contains miscellaneous scripts that are useful for working on or with cslib.
When adding a new script, please make sure to document it here, so other readers have a chance
to learn about it as well!

## Current scripts and their purpose

**Documentation generation**
- `gendocs.sh`
  Generates the documentation for cslib using `lake`.

**Devcontainer helpers**
- `setup-mistral-vibe.sh`
  Installs the Mistral Vibe VS Code extension (`mistralai.mistral-vibe-code`) if
  missing and ensures required Mistral config entries for the `lean` agent and the `lean-lsp` MCP server are present.

  **Usage:**
  ```bash
  ./scripts/setup-mistral-vibe.sh
  ```

  **Optional environment variable:**
  - `MISTRAL_CONFIG_FILE`: Override the path to `config.toml`.

**Init Imports**
- `CheckInitImports.lean` (run by `lake exe checkInitImports`) checks that all files publicly import
  `Cslib.Init`, directly or transitively.
