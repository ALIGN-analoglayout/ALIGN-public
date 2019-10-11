from flask import Flask, request, Response
from flask_cors import CORS, cross_origin
app = Flask(__name__)
cors = CORS(app)
app.config['CORS_HEADERS'] = 'Content-Type'


import json

@app.route('/post',methods=['POST'])
@cross_origin()
def save_using_post():
    print(request.method)
    with open( "__json", "wt") as fp:
        json.dump( request.get_json(), fp, indent=2)
    return 'Posted'

@app.route('/get',methods=['GET'])
@cross_origin()
def load_using_get():
    print(request.method)
    with open( "__json", "rt") as fp:
        resp = Response(fp.read(), status=200, mimetype='application/json')
        return resp
    return Response("", status=401)

if __name__ == "__main__":
    app.run(debug=True,host='0.0.0.0')
