from django.db import migrations, models


class Migration(migrations.Migration):

    dependencies = [
        ('adsbee_swarm', '0003_sample_range'),
    ]

    operations = [
        migrations.RemoveField(model_name='sample', name='range_map'),
        migrations.RemoveField(model_name='sample', name='unit_m'),
    ]
