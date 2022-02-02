from align.schema.model import Model

PDK_MODELS = list()

PDK_MODELS.append(
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
            'PARALLEL': 1,  # Get rid of this hack
            'STACK': 1  # Get rid of this hack
            }
    )
)

PDK_MODELS.append(
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
            'PARALLEL': 1,  # Get rid of this hack
            'STACK': 1  # Get rid of this hack
            }
    )
)

PDK_MODELS.append(
    Model(
        name='TFR',
        pins=['A', 'B'],
        prefix='',
        parameters={'W': 0, 'L': 0},
    )
)
