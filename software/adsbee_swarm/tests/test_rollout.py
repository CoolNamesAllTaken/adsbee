import pytest

from adsbee_swarm import rollout, services
from adsbee_swarm.models import Device

from .conftest import post_report

pytestmark = pytest.mark.django_db


@pytest.fixture
def bees(owner):
    def make(uid, label='', product='adsbee_1090', version='0.9.1'):
        return Device.objects.create(account=owner.account, product=product, unique_id=uid, label=label,
                                     versions={'rp2040': version})
    return {'a': make('000000000000000A', 'roof'), 'b': make('000000000000000B', 'roof'),
            'c': make('000000000000000C', 'shed'), 'm': make('000000000000000D', product='adsbee_1421')}


def _targets(bees):
    return {key: (rollout.target(d) or {}).get('tag') for key, d in bees.items()}


def test_no_rollout_no_target(bees):
    assert _targets(bees) == {'a': None, 'b': None, 'c': None, 'm': None}


def test_all_bees_of_the_product(owner, bees):
    services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.2'})
    assert _targets(bees) == {'a': '0.9.2', 'b': '0.9.2', 'c': '0.9.2', 'm': None}
    assert rollout.target(bees['a']) == {'tag': '0.9.2', 'channel': 'stable'}


def test_a_label_or_chosen_bees(owner, bees):
    services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.2', 'scope': 'label',
                                            'label': 'roof'})
    assert _targets(bees) == {'a': '0.9.2', 'b': '0.9.2', 'c': None, 'm': None}
    services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.3-rc1', 'scope': 'devices',
                                            'devices': [bees['c'].pk]})
    assert _targets(bees) == {'a': '0.9.2', 'b': '0.9.2', 'c': '0.9.3-rc1', 'm': None}
    assert rollout.target(bees['c'])['channel'] == 'rc'


def test_test_bees_first_then_promote(owner, bees):
    plan = services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.2',
                                                   'test_devices': [bees['a'].pk]})
    assert plan.stage == 'test'
    assert _targets(bees) == {'a': '0.9.2', 'b': None, 'c': None, 'm': None}
    services.rollout_action(plan, 'promote')
    assert _targets(bees) == {'a': '0.9.2', 'b': '0.9.2', 'c': '0.9.2', 'm': None}


def test_pause_offers_nothing_and_does_not_hand_back_to_an_older_rollout(owner, bees):
    services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.1'})
    newer = services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.2'})
    services.rollout_action(newer, 'pause')
    assert _targets(bees)['a'] is None
    services.rollout_action(newer, 'resume')
    assert _targets(bees)['a'] == '0.9.2'


def test_cancel_hands_back_to_the_older_rollout(owner, bees):
    services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.1'})
    newer = services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.2'})
    services.rollout_action(newer, 'cancel')
    assert _targets(bees)['a'] == '0.9.1'
    with pytest.raises(services.SwarmError):
        services.rollout_action(newer, 'resume')


def test_another_accounts_rollout_never_targets_my_bees(other, bees):
    services.create_rollout(other.account, {'product': 'adsbee_1090', 'tag': '9.9.9'})
    assert _targets(bees)['a'] is None


def test_bees_of_another_account_cannot_be_chosen(owner, other, bees):
    theirs = Device.objects.create(account=other.account, product='adsbee_1090', unique_id='00000000000000FF')
    with pytest.raises(services.SwarmError, match='Not every device'):
        services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.2', 'scope': 'devices',
                                                'devices': [theirs.pk]})


@pytest.mark.parametrize('data, why', [
    ({'product': 'toaster', 'tag': '1'}, 'product'), ({'product': 'adsbee_1090', 'tag': 'a b'}, 'tag'),
    ({'product': 'adsbee_1090', 'tag': '1', 'scope': 'label'}, 'label'),
    ({'product': 'adsbee_1090', 'tag': '1', 'scope': 'devices'}, 'Choose'),
])
def test_bad_rollouts(owner, data, why):
    with pytest.raises(services.SwarmError, match=why):
        services.create_rollout(owner.account, data)


def refuse_tag(product, tag):
    return None if tag == '0.9.2' else f'{tag} is not a release'


def test_the_host_validates_tags(owner, settings):
    settings.ADSBEE_SWARM_TAG_VALIDATOR = 'tests.test_rollout.refuse_tag'
    with pytest.raises(services.SwarmError, match='not a release'):
        services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.0.1'})
    services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.2'})


def test_the_report_response_carries_the_target(client, owner, bee):
    assert post_report(client, owner.token, bee.report()).json()['firmware'] is None
    device = Device.objects.get()
    services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.2',
                                            'test_devices': [device.pk]})
    assert post_report(client, owner.token, bee.report()).json()['firmware'] == {'tag': '0.9.2', 'channel': 'stable'}


def test_progress_counts_bees_on_the_tag(owner, bees):
    plan = services.create_rollout(owner.account, {'product': 'adsbee_1090', 'tag': '0.9.1'})
    assert rollout.progress(plan) == {'targeted': 3, 'on_tag': 3, 'auto_update': 0}
