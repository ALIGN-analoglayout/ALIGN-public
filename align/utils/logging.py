import logging.config
import pathlib

def configure_logger(dir_name='LOG'):
    (pathlib.Path.cwd() / dir_name).mkdir(exist_ok=True)
    logging.config.fileConfig(pathlib.Path(__file__).parent.parent / 'config' / 'logging.ini', disable_existing_loggers=False)
