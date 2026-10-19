from io import StringIO

import pytest
from django.contrib.auth import get_user_model
from django.core.management import CommandError, call_command

from adsbee_fleet import protocol, services
from adsbee_fleet.models import Account, token_hash
from adsbee_fleet.simulator import Bee

pytestmark = pytest.mark.django_db


def test_create_account_without_a_password_is_invite_only():
    account, token = services.create_account('dana', email='d@example.com', privileges=['fleet', 'wiggler'])
    assert not account.user.has_usable_password()
    assert account.privileges == ['fleet', 'wiggler'] and account.has('wiggler')
    assert account.enroll_token_hash == token_hash(token) and token not in str(Account.objects.values())


def test_privileges_are_checked_and_extensible(settings):
    account, _ = services.create_account('erin')
    with pytest.raises(services.FleetError):
        services.grant(account, 'teleport')
    settings.ADSBEE_FLEET_PRIVILEGES = {'fleet': 'Fleet', 'teleport': 'Teleport'}
    assert services.grant(account, 'teleport').has('teleport')


def test_disable_blocks_login_and_tokens():
    account, token = services.create_account('fred', password='pw')
    services.set_disabled(account)
    assert not get_user_model().objects.get(username='fred').is_active
    assert services.account_by_enroll_token(token) is None
    services.set_disabled(account, False)
    assert services.account_by_enroll_token(token) == account


def test_the_account_command():
    out = StringIO()
    call_command('fleet_account', 'create', 'gus', '--privilege', 'fleet', stdout=out)
    assert 'enroll token:' in out.getvalue()
    call_command('fleet_account', 'grant', 'gus', '--privilege', 'wiggler', stdout=StringIO())
    assert Account.objects.get().privileges == ['fleet', 'wiggler']
    call_command('fleet_account', 'disable', 'gus', stdout=StringIO())
    assert Account.objects.get().disabled
    with pytest.raises(CommandError):
        call_command('fleet_account', 'grant', 'nobody', stdout=StringIO())


def test_simulated_reports_parse_and_look_like_a_receiver():
    bee = Bee.make(2)
    report = protocol.parse(bee.report())
    assert report.rx_position['alt_m'] == bee.alt_m and report.seq == 1
    high = max(m for i, m in report.ranges.items() if i >= 11 * 36)
    low = max((m for i, m in report.ranges.items() if i < 36), default=0)
    assert high > low and high <= 400_000
