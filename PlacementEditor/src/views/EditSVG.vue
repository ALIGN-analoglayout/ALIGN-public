<template>
  <div>
    <h1>SVG-Based Placment Editor</h1>
    <div>
      <button @click="getContent">Load</button>
      <button @click="postContent">Save</button>
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
            :transform="`translate(${c.ox} ${c.oy})`"
          >
            <path
              :d="`M 0 0 h ${c.w} v ${c.h} h ${-c.w} v ${-c.h}`"
              stroke="black"
              :fill="c.fill"
              @mousedown="doStart($event, c, idx, 2)"
            ></path>
            <g :transform="`matrix(1 0 0 -1 ${c.w / 2} 24)`">
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
    return {
      width: 960, // 720 * 4 / 3 = 240 * 4 = 960
      height: 720,
      scale: 0.8, // 18*50 = 900 * 4/5 = 180*4 = 720
      step: 50,
      r: 20,
      ny: 18,
      nx: 24,
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
        w: 4 * this.step,
        h: 1 * this.step,
        ox: 4 * this.step,
        oy: (i + 4) * this.step,
        fill: '#ffe0e0',
        nm: nms[i]
      })
    }
    for (let i = 0; i <= this.ny; i += 1) {
      this.hgridlines.push({
        cy: this.step * i,
        x0: 0,
        x1: this.step * this.nx
      })
    }
    for (let j = 0; j <= this.nx; j += 1) {
      this.vgridlines.push({
        cx: this.step * j,
        y0: 0,
        y1: this.step * this.ny
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
    roundNearestGrid: function(offset) {
      return Math.round(offset / this.step) * this.step
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
          dg.ox = this.getEventX(event) - this.offx
          dg.oy = this.getEventY(event) - this.offy
        }
      }
    },
    doStart: function(event, c, idx, code) {
      console.log('Start: ', event, c, idx, code)
      this.code = code
      this.moving = true
      this.moving_idx = idx
      let dg = this.leaves[this.moving_idx]
      this.offx = this.getEventX(event) - dg.ox
      this.offy = this.getEventY(event) - dg.oy
    },
    doEnd: function() {
      if (this.moving) {
        const e = Elastic.easeOut.config(1, 0.3)
        const t = 0.5
        let dg = this.leaves[this.moving_idx]

        if (this.code == 2) {
          let targetX = this.roundNearestGrid(dg.ox)
          let targetY = this.roundNearestGrid(dg.oy)
          TweenMax.to(dg, t, {
            ox: targetX,
            oy: targetY,
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
