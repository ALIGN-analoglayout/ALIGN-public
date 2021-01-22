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
        for x in logging.getLogger().handlers:
            if isinstance(x, logging.handlers.RotatingFileHandler):
                x.doRollover()

class StreamLogger(object):
    """
    Stream object that redirects writes to logger
    """
    def __init__(self, name, level='INFO'):
        self.logger = logging.getLogger(name)
        self.level = getattr(logging, level)
        self.linebuf = ''

    def write(self, buf):
        for line in buf.rstrip().splitlines():
                self.logger.log(self.level, line.rstrip())

    def flush(self):
        pass
