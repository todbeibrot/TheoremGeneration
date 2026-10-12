# Simple API for versioned file names and paths.

import re
from pathlib import Path


def _normalize_ext(ext: str) -> str:
    """
    Normalize a file extension.

    Examples:
        "txt"  -> ".txt"
        ".txt" -> ".txt"
        ""     -> ""
    """
    if not ext:
        return ""
    return ext if ext.startswith(".") else f".{ext}"


def version_name(prefix: str, n: int, ext: str = "") -> str:
    """
    Return a versioned file name of the form '<prefix>_<N><ext>'.

    The version number is zero-padded to 6 digits as long as n <= 999999.
    Larger numbers are appended without padding.

    Examples:
        version_name("model", 42) -> "model_000042"
        version_name("model", 42, ".txt") -> "model_000042.txt"
        version_name("model", 1200000) -> "model_1200000"
    """
    ext = _normalize_ext(ext)
    if n <= 999999:
        return f"{prefix}_{n:06d}{ext}"
    return f"{prefix}_{n}{ext}"


def latest_version(prefix: str, directory: str | Path = ".", ext: str = "") -> int | None:
    """
    Return the largest saved version number for files matching the versioned naming scheme.

    Only files matching '<prefix>_<N><ext>' are considered.

    Args:
        prefix: File prefix, e.g. 'model'.
        directory: Directory to search in.
        ext: File extension, with or without leading dot.

    Returns:
        The largest version number, or None if no matching file exists.

    Example:
        If the directory contains
            model_000001.txt
            model_000042.txt
            model_000113.txt
        then
            latest_version("model", "models", ".txt")
        returns 113.
    """
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    ext = _normalize_ext(ext)
    pattern = re.compile(rf"^{re.escape(prefix)}_(\d+){re.escape(ext)}$")

    max_n = None
    for p in directory.iterdir():
        m = pattern.match(p.name)
        if m:
            n = int(m.group(1))
            if max_n is None or n > max_n:
                max_n = n

    return max_n


def latest_version_path(prefix: str, directory: str | Path = ".", ext: str = "") -> Path | None:
    """
    Return the path to the latest saved version.

    Args:
        prefix: File prefix, e.g. 'model'.
        directory: Directory to search in.
        ext: File extension, with or without leading dot.

    Returns:
        The path to the latest matching file, or None if no matching file exists.
    """
    directory = Path(directory)
    v = latest_version(prefix, directory, ext)
    if v is None:
        return None
    return directory / version_name(prefix, v, ext)


def next_version(prefix: str, directory: str | Path = ".", ext: str = "") -> int:
    """
    Return the next free version number.

    Args:
        prefix: File prefix, e.g. 'model'.
        directory: Directory to search in.
        ext: File extension, with or without leading dot.

    Returns:
        0 if no matching file exists, otherwise the latest version plus 1.
    """
    v = latest_version(prefix, directory, ext)
    return 0 if v is None else v + 1


def next_version_path(prefix: str, directory: str | Path = ".", ext: str = "") -> Path:
    """
    Return the path for the next free version.

    Args:
        prefix: File prefix, e.g. 'model'.
        directory: Directory to place the file in.
        ext: File extension, with or without leading dot.

    Returns:
        The path corresponding to the next free version.

    Example:
        If the latest file is 'model_000113.txt', then
            next_version_path("model", "models", ".txt")
        returns Path("models/model_000114.txt").
    """
    directory = Path(directory)
    v = next_version(prefix, directory, ext)
    return directory / version_name(prefix, v, ext)