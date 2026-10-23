"""Range maps move to one row per sample and protocol; existing maps become protocol `aircraft`."""
import django.db.models.deletion
from django.db import migrations, models

from adsbee_swarm import ranges


def forward(apps, schema_editor):
    Sample = apps.get_model('adsbee_swarm', 'Sample')
    SampleRange = apps.get_model('adsbee_swarm', 'SampleRange')
    batch = []
    for pk, unit, blob in Sample.objects.exclude(range_map=None).values_list('pk', 'unit_m', 'range_map').iterator():
        if blob:
            batch.append(SampleRange(sample_id=pk, protocol='aircraft', unit_m=unit, range_map=bytes(blob)))
        if len(batch) >= 1000:
            SampleRange.objects.bulk_create(batch)
            batch = []
    SampleRange.objects.bulk_create(batch)


def backward(apps, schema_editor):
    """Aircraft maps merged back into the sample (coarsest unit); Remote ID maps are lost."""
    Sample = apps.get_model('adsbee_swarm', 'Sample')
    SampleRange = apps.get_model('adsbee_swarm', 'SampleRange')
    merged = {}
    for row in SampleRange.objects.filter(protocol__in=ranges.SOURCES['aircraft']).iterator():
        unit, values = merged.get(row.sample_id, (0, {}))
        ranges.merge(values, ranges.unpack(row.range_map, row.unit_m))
        merged[row.sample_id] = (max(unit, row.unit_m), values)
    for pk, (unit, values) in merged.items():
        Sample.objects.filter(pk=pk).update(unit_m=unit, range_map=ranges.pack(values, unit) if values else None)


class Migration(migrations.Migration):

    dependencies = [
        ('adsbee_swarm', '0002_position_guards'),
    ]

    operations = [
        migrations.CreateModel(
            name='SampleRange',
            fields=[
                ('id', models.BigAutoField(auto_created=True, primary_key=True, serialize=False, verbose_name='ID')),
                ('protocol', models.CharField(max_length=16)),
                ('unit_m', models.PositiveIntegerField(default=2000)),
                ('range_map', models.BinaryField()),
                ('sample', models.ForeignKey(on_delete=django.db.models.deletion.CASCADE, related_name='range_rows', to='adsbee_swarm.sample')),
            ],
            options={
                'constraints': [models.UniqueConstraint(fields=('sample', 'protocol'), name='swarm_sample_range_unique')],
            },
        ),
        migrations.RunPython(forward, backward),
    ]
