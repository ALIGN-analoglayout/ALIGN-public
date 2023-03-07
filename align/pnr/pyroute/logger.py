import logging

# Create a custom logger
logging.basicConfig(filename='pnr.log', filemode='w',
        format='[%(asctime)s %(filename)s:%(funcName)s %(levelname)s]: %(message)s',
        datefmt='%H:%M:%S', level=logging.DEBUG)
logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

