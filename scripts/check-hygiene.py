"""Reject tracked private material, local configuration and build outputs."""

from pathlib import PurePosixPath
import subprocess


PRIVATE_DIRS = {
    "private", "scratch", "outreach", "drafts", ".claude", ".codex",
    ".vscode", ".idea", ".venv", ".lake", "__pycache__",
    ".pytest_cache", ".mypy_cache", "rebuilt",
}
PRIVATE_FILES = {".ds_store", "thumbs.db", ".env", "rebuilt.jsonl"}
GENERATED_LEAN = {"formal/median11/certificatedata.lean"}
BLOCKED_SUFFIXES = {
    ".pem", ".key", ".p12", ".pfx", ".swp", ".tmp", ".zip", ".log",
    ".aux", ".blg", ".fls", ".fdb_latexmk", ".olean", ".ilean", ".pyc",
}


def prohibited(path: str) -> bool:
    file = PurePosixPath(path.casefold())
    return (
        bool(PRIVATE_DIRS.intersection(file.parts[:-1]))
        or bool(PRIVATE_FILES.intersection(file.parts))
        or any(part.startswith(".env.") for part in file.parts)
        or file.suffix in BLOCKED_SUFFIXES
        or str(file) in GENERATED_LEAN
        or file.parts[:3] == ("formal", "median11", "kerneldata")
    )


def main() -> None:
    tracked = subprocess.check_output(["git", "ls-files", "-z"]).decode().split("\0")
    blocked = [path for path in tracked if path and prohibited(path)]
    if blocked:
        raise SystemExit("Prohibited tracked paths:\n" + "\n".join(blocked))
    print("Tracked paths pass repository hygiene checks.")


if __name__ == "__main__":
    main()
