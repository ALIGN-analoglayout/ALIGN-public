# PlacementEditor

Since it takes a while to build a nodejs image, we can this on docker hub:
```bash
docker build -f Dockerfile.nodejs_ubuntu -t darpaalign/nodejs_ubuntu:02Apr19 .
docker push darpaalign/nodejs_ubuntu:02Apr19
```

To build an example docker image of the client:
```bash
docker build -t darpaalign/placement_editor_client .
```

To run tests for the client:
```bash
docker run -it darpaalign/placement_editor_client bash -c "npm run test"
```

To build one for the server:
```bash
(cd server; docker build -t darpaalign/placement_editor_server .)
```

To run:
```bash
docker run -p 5000:5000 -d darpaalign/placement_editor_server bash -c "source sympy/bin/activate && cd public && python server.py"
docker run -p 8086:8080 -d darpaalign/placement_editor_client
```
Then connect to `localhost:8086`


### Compiles and hot-reloads for development
```
npm run serve
```

### Compiles and minifies for production
```
npm run build
```

### Run your tests
```
npm run test
```

### Lints and fixes files
```
npm run lint
```
