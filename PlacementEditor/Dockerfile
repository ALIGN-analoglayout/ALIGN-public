FROM ubuntu:18.04

RUN \
  apt-get update && apt-get install -y nodejs npm curl python make build-essential && rm -rf /var/lib/apt/lists/*

RUN \
  npm install -g npm@latest && \
  npm install -g http-server

WORKDIR /app

COPY package*.json ./

RUN \
  npm install

COPY . .

RUN \
  npm run build

EXPOSE 8080
CMD [ "http-server", "dist"]

