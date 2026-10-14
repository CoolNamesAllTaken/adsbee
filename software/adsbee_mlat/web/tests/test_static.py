from django.core.management import call_command


def test_collectstatic_with_production_storage(settings, tmp_path):
    settings.STATIC_ROOT = tmp_path
    settings.STORAGES = {**settings.STORAGES,
                         "staticfiles": {"BACKEND": "whitenoise.storage.CompressedManifestStaticFilesStorage"}}
    call_command("collectstatic", "--noinput", verbosity=0)
    assert (tmp_path / "staticfiles.json").exists()
