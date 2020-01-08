import logging.config
import pathlib
import configparser

def configure_logging():
    cfg = configparser.ConfigParser()
    cfg.read(pathlib.Path(__file__).parent.parent / 'config' / 'logging.ini')
    logfile = pathlib.Path(cfg['handler_fileHandler']['args'].split("'")[1])
    logfile.parent.mkdir(exist_ok=True)
    rollover = logfile.is_file()
    logging.config.fileConfig(cfg, disable_existing_loggers=False)
    if rollover:
        [x.doRollover() for x in logging.getLogger().handlers \
        if isinstance(x, logging.handlers.RotatingFileHandler)]
