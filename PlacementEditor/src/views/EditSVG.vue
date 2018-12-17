<template>
  <div>
    <h1>SVG-Based Placement Editor</h1>
    <div>
      <button @click="getContent">Load</button>
      <button @click="postContent">Save</button>
    </div>
    <div class="value-tbl" v-for="(c, idx) in leaves" :key="`i-${idx}`">
      <span>{{ c.nm }}</span> <input v-model="c.w" /> <input v-model="c.h" />
      <input v-model="c.transformation.oX" />
      <input v-model="c.transformation.oY" />
      <input v-model="c.transformation.sX" />
      <input v-model="c.transformation.sY" />
    </div>
    <div>
      <svg
        :width="width"
        :height="height"
        @mousemove="doMove($event)"
        @mouseup="doEnd($event)"
      >
        <g :transform="`matrix(${scale} 0 0 ${-scale} 0 ${height})`">
          <g v-for="(l, idx) in hgridlines" :key="`h-${idx}`">
            <line
              :x1="l.x0"
              :y1="l.cy"
              :x2="l.x1"
              :y2="l.cy"
              stroke="black"
              stroke-dasharray="10 4"
            ></line>
          </g>
          <g v-for="(l, idx) in vgridlines" :key="`v-${idx}`">
            <line
              :x1="l.cx"
              :y1="l.y0"
              :x2="l.cx"
              :y2="l.y1"
              stroke="black"
              stroke-dasharray="10 4"
            ></line>
          </g>
          <g
            v-for="(c, idx) in leaves"
            :key="`d-${idx}`"
            :transform="
              `translate(${c.transformation.oX} ${c.transformation.oY}) scale(${
                c.transformation.sX
              } ${c.transformation.sY})`
            "
          >
            <path
              :d="`M 0 0 h ${c.w} v ${c.h} h ${-c.w} v ${-c.h}`"
              stroke="black"
              :fill="c.fill"
              @mousedown="doStart($event, c, idx, 2)"
            ></path>
            <g :transform="`matrix(1 0 0 -1 ${c.w / 2 - 48} ${c.h / 2 + 0})`">
              <text :x="0" :y="0" style="font: 24px sans-serif;">
                {{ c.nm }}
              </text>
            </g>
          </g>
        </g>
      </svg>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import { Elastic, TweenMax } from 'gsap'
export default {
  data: function() {
    const width = 960
    const height = 720
    const step = 50
    const stepsPerXStep = 4
    const stepsPerYStep = 8
    const stepx = stepsPerXStep * step
    const stepy = stepsPerYStep * step
    let ny = 4
    let nx = 6
    var scale

    if (stepsPerYStep * ny * width > stepsPerXStep * nx * height) {
      // ny is constraining
      nx = stepsPerYStep * Math.round((stepsPerXStep * ny * width) / height)
      scale = height / (ny * stepy)
    } else {
      ny = stepsPerXStep * Math.round((stepsPerYStep * nx * height) / width)
      scale = width / (nx * stepx)
    }

    return {
      width: width,
      height: height,
      scale: scale,
      stepx: stepx,
      stepy: stepy,
      ny: ny,
      nx: nx,
      moving: false,
      moving_idx: undefined,
      code: undefined,
      offx: undefined,
      offy: undefined,
      leaves: [],
      hgridlines: [],
      vgridlines: [],
      errors: []
    }
  },
  created: function() {
    console.log('Running created...')
    this.dogbones = []
    var nms = ['ref', '1a', '1b', '2', '4']
    for (let i = 0; i < 5; i += 1) {
      this.leaves.push({
        w: 4 * this.stepx,
        h: 1 * this.stepy,
        transformation: {
          oX: 8 * this.stepx,
          oY: (2 * i + 4) * this.stepy,
          sX: 1,
          sY: 1
        },
        fill: '#ffe0e0',
        nm: nms[i]
      })
    }
    for (let i = 0; i <= this.ny; i += 1) {
      this.hgridlines.push({
        cy: this.stepy * i,
        x0: 0,
        x1: this.stepx * this.nx
      })
    }
    for (let j = 0; j <= this.nx; j += 1) {
      this.vgridlines.push({
        cx: this.stepx * j,
        y0: 0,
        y1: this.stepy * this.ny
      })
    }
  },
  methods: {
    getContent: function() {
      axios
        .get('http://localhost:5000/get')
        .then(response => {
          this.leaves = response['data']
        })
        .catch(e => {
          this.errors.push(e)
        })
    },
    postContent: function() {
      axios
        .post('http://localhost:5000/post', this.leaves, {
          headers: { 'Content-Type': 'application/json' }
        })
        .then(response => {
          console.log('Saved: ', response)
        })
        .catch(e => {
          this.errors.push(e)
        })
    },
    roundNearestGridX: function(offset) {
      return Math.round(offset / this.stepx) * this.stepx
    },
    roundNearestGridY: function(offset) {
      return Math.round(offset / this.stepy) * this.stepy
    },
    getEventX: function(event) {
      return event.offsetX / this.scale
    },
    getEventY: function(event) {
      return (this.height - event.offsetY) / this.scale
    },
    doMove: function(event) {
      if (this.moving) {
        let dg = this.leaves[this.moving_idx]
        /*
        s 0  0      1/s 0    0       1 0 0
        0 -s h      0   -1/s h/s  =  0 1 0
        0 0  1      0   0    1       0 0 1
        */
        if (this.code == 2) {
          dg.transformation.oX = this.getEventX(event) - this.offx
          dg.transformation.oY = this.getEventY(event) - this.offy
        }
      }
    },
    doKeyup: function(event) {
      console.log('event', event)
    },
    doStart: function(event, c, idx, code) {
      console.log('Start: ', event, c, idx, code)
      this.code = code
      this.moving = true
      this.moving_idx = idx
      let dg = this.leaves[this.moving_idx]
      this.offx = this.getEventX(event) - dg.transformation.oX
      this.offy = this.getEventY(event) - dg.transformation.oY
    },
    doEnd: function() {
      if (this.moving) {
        const e = Elastic.easeOut.config(1, 0.3)
        const t = 0.5
        let dg = this.leaves[this.moving_idx]

        if (this.code == 2) {
          let targetX = this.roundNearestGridX(dg.transformation.oX)
          let targetY = this.roundNearestGridY(dg.transformation.oY)
          TweenMax.to(dg.transformation, t, {
            oX: targetX,
            oY: targetY,
            ease: e
          })
        }
        this.moving = false
        this.moving_idx = undefined
        this.code = undefined
        this.offset = undefined
      }
    }
  }
}
</script>

<style>
.value-tbl > input {
  width: 10ex;
}
.value-tbl > span {
  width: 10ex;
  border-right: 15ex;
}
</style>
