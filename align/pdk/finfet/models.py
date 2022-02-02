from align.schema.model import Model


def pdk_models():
    models = list()
    models.append(
        Model(
            name='NMOS',
            pins=['D', 'G', 'S', 'B'],
            prefix='',
            parameters={
                'W': 0,
                'L': 0,
                'NFIN': 1,
                'NF': 2,
                'M': 1,
                'STACK': 1
                }
        )
    )
    models.append(
        Model(
            name='PMOS',
            pins=['D', 'G', 'S', 'B'],
            prefix='',
            parameters={
                'W': 0,
                'L': 0,
                'NFIN': 1,
                'NF': 2,
                'M': 1,
                'STACK': 1
                }
        )
    )

    models.append(
        Model(
            name='TFR',
            pins=['A', 'B'],
            prefix='',
            parameters={'W': 0, 'L': 0},
        )
    )
    return models
