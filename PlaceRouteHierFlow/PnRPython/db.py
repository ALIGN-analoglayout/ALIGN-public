import json

if __name__ == "__main__":
    with open("../telescopic_ota-freeze.json","rt") as fp:
        d = json.load(fp)

    print( list(d.keys()))
