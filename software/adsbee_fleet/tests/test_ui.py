from io import StringIO

import pytest
from django.core.management import call_command

from adsbee_fleet import services
from adsbee_fleet.models import Device, Rollout

pytestmark = pytest.mark.django_db


@pytest.fixture
def signed_in(client, owner):
    call_command('fleet_simulate', 'alice', '--bees', '3', '--hours', '30', stdout=StringIO())
    client.login(username='alice', password='pw')
    return client


def test_pages_need_a_login_and_the_fleet_privilege(client, owner):
    assert client.get('/').status_code == 302
    client.login(username='alice', password='pw')
    services.revoke(owner.account, 'fleet')
    assert client.get('/').status_code == 403


def test_device_list_and_map(signed_in):
    page = signed_in.get('/?w=24h').content.decode()
    assert page.count('href="') > 3 and 'id="markers"' in page and 'Attic' in page
    assert 'leaflet@1.9.4' in page


def test_device_page_draws_a_polar_plot_per_band(signed_in):
    device = Device.objects.first()
    page = signed_in.get(f'/devices/{device.pk}/').content.decode()
    assert page.count('<svg') == 13 and 'class="wedge"' in page and '≥40k ft' in page


def test_device_edit_remove_restore(signed_in):
    device = Device.objects.first()
    signed_in.post(f'/devices/{device.pk}/', {'action': 'save', 'label': 'Mast', 'note': '', 'lat': '37.1', 'lon': '-122'})
    device.refresh_from_db()
    assert (device.label, device.lat) == ('Mast', 37.1)
    signed_in.post(f'/devices/{device.pk}/', {'action': 'remove'})
    device.refresh_from_db()
    assert device.removed
    signed_in.post(f'/devices/{device.pk}/', {'action': 'restore'})
    device.refresh_from_db()
    assert not device.removed


def test_another_accounts_device_page_is_404(signed_in, other):
    theirs = Device.objects.create(account=other.account, product='adsbee_1090', unique_id='00000000000000FF')
    assert signed_in.get(f'/devices/{theirs.pk}/').status_code == 404


def test_rollout_page(signed_in):
    ids = list(Device.objects.values_list('pk', flat=True))
    signed_in.post('/rollouts/', {'action': 'create', 'product': 'adsbee_1090', 'tag': '0.9.2', 'scope': 'all',
                                  'test_devices': [str(ids[0])]})
    plan = Rollout.objects.get()
    assert plan.stage == 'test'
    signed_in.post('/rollouts/', {'action': 'promote', 'rollout': plan.pk})
    plan.refresh_from_db()
    assert plan.stage == 'all'
    assert '0.9.2' in signed_in.get('/rollouts/').content.decode()


def test_account_page_shows_the_at_command_once(signed_in):
    page = signed_in.post('/account/action/', {'action': 'rotate'}).content.decode()
    assert 'AT+FLEET=1,http://testserver,' in page
    assert 'AT+FLEET=1' not in signed_in.get('/account/').content.decode()


def test_login_page_renders(client, db):
    assert 'password' in client.get('/login/').content.decode()
