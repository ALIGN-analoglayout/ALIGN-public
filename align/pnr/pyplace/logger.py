import logging

# Create a custom logger
logging.basicConfig(filename='pnr.log',
                            filemode='a',
                            format='[%(asctime)s %(name)s %(levelname)s]: %(message)s',
                            datefmt='%H:%M:%S',
                            level=logging.DEBUG)
logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)

