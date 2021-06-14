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

def reconfigure_loglevels(file_level=None, console_level=None):
    if file_level and console_level:
        logging.getLogger().setLevel(min(logging.getLevelName(file_level), logging.getLevelName(console_level)))
    elif file_level:
        logging.getLogger().setLevel(logging.getLevelName(file_level))
    elif console_level:
        logging.getLogger().setLevel(logging.getLevelName(console_level))

    if file_level:
        handler = next(x for x in logging.getLogger().handlers if isinstance(x, logging.handlers.RotatingFileHandler))
        handler.setLevel(logging.getLevelName(file_level))

    if console_level:
        handler = next(x for x in logging.getLogger().handlers if isinstance(x, logging.StreamHandler))
        handler.setLevel(logging.getLevelName(console_level))

def get_loglevels():
    filehandler = next(x for x in logging.getLogger().handlers if isinstance(x, logging.handlers.RotatingFileHandler))
    consolehandler = next(x for x in logging.getLogger().handlers if isinstance(x, logging.StreamHandler))
    return logging.getLevelName(filehandler.level), logging.getLevelName(consolehandler.level)

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
