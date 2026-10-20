import os

from example_site.settings import *  # noqa: F401,F403

if os.environ.get('SWARM_TEST_POSTGRES'):
    DATABASES = {'default': {'ENGINE': 'django.db.backends.postgresql', 'HOST': '127.0.0.1', 'PORT': os.environ.get('SWARM_TEST_POSTGRES_PORT', '5432'),
                             'NAME': 'swarm', 'USER': 'swarm', 'PASSWORD': 'swarm'}}
else:
    DATABASES = {'default': {'ENGINE': 'django.db.backends.sqlite3', 'NAME': ':memory:'}}
CACHES = {'default': {'BACKEND': 'django.core.cache.backends.locmem.LocMemCache'}}
PASSWORD_HASHERS = ['django.contrib.auth.hashers.MD5PasswordHasher']
SESSION_COOKIE_SECURE = CSRF_COOKIE_SECURE = False
