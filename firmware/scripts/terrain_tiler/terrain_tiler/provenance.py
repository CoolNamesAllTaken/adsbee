"""Capture data-source provenance for a `world.map` build.

Records the exact version of every input so a built archive is traceable for
reproducibility and licensing: ETOPO elevation, the two Natural Earth vector
downloads, plus tiler build metadata. Read automatically from the data cache at
build time (never hand-typed). Emitted as a compact JSON blob referenced by the
PyramidHeader's provenance_offset/len, so it stays human-readable and extensible.
"""
import json
import os
import subprocess


def _read_version_file(path):
    try:
        with open(path, "r") as f:
            return f.read().strip()
    except OSError:
        return None


def _git_commit(repo_dir):
    try:
        out = subprocess.run(
            ["git", "-C", repo_dir, "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, timeout=5)
        if out.returncode == 0:
            return out.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    return None


def collect(dem_path, ne_physical_dir, ne_cultural_dir, build_date,
            *, format_version, num_levels, finest_samples_per_deg, elev_step_m,
            vw_px_tolerance=None, tiler_version=None):
    """Build the provenance dict. build_date is passed in (callers must not use
    Date.now() inside worker processes); format the ISO date string upstream."""
    here = os.path.dirname(os.path.abspath(__file__))
    prov = {
        "format": "world.map",
        "format_version": format_version,
        "generator": {
            "tool": "terrain-tiler",
            "version": tiler_version,
            "git_commit": _git_commit(here),
            "build_date": build_date,
        },
        "elevation": {
            "source": "ETOPO 2022 Global Relief Model",
            "publisher": "NOAA National Centers for Environmental Information",
            "doi": "10.25921/fd45-gt74",
            "file": os.path.basename(dem_path),
            # e.g. ETOPO_2022_v1_30s_N90W180_surface.tif -> variant "30s surface"
            "variant": _etopo_variant(dem_path),
        },
        "vectors": {
            "source": "Natural Earth 1:10m",
            "url": "https://www.naturalearthdata.com",
            "physical_version": _read_version_file(
                os.path.join(ne_physical_dir, "VERSION")),
            "cultural_version": _read_version_file(
                os.path.join(ne_cultural_dir, "VERSION")),
        },
        "encoding": {
            "num_levels": num_levels,
            "finest_samples_per_deg": finest_samples_per_deg,
            "elev_step_m": elev_step_m,
            "vw_px_tolerance": vw_px_tolerance,
        },
    }
    return prov


def _etopo_variant(dem_path):
    name = os.path.basename(dem_path).lower()
    res = "30s" if "30s" in name else ("60s" if "60s" in name else "unknown")
    kind = "surface" if "surface" in name else ("bed" if "bed" in name else "unknown")
    return f"{res} {kind}"


def to_blob(prov):
    """Serialize to bytes for the archive (compact but readable JSON)."""
    return json.dumps(prov, separators=(",", ":"), sort_keys=True).encode("utf-8")


def summary_lines(prov):
    """Human-readable lines for CLI output / README."""
    e, v, g = prov["elevation"], prov["vectors"], prov["generator"]
    return [
        f"elevation: {e['source']} ({e['variant']}) — {e['file']}",
        f"vectors:   {v['source']} physical v{v['physical_version']} / "
        f"cultural v{v['cultural_version']}",
        f"generator: terrain-tiler {g['version'] or ''} "
        f"commit={g['git_commit'] or '?'} built {g['build_date']}",
    ]
