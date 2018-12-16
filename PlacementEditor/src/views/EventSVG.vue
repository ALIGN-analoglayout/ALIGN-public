<template>
  <div>
    <h1>SVG-Based Dogbone Editor</h1>
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
            />
          </g>
          <g v-for="(l, idx) in vgridlines" :key="`v-${idx}`">
            <line
              :x1="l.cx"
              :y1="l.y0"
              :x2="l.cx"
              :y2="l.y1"
              stroke="black"
              stroke-dasharray="10 4"
            />
          </g>
          <g
            v-for="(c, idx) in dogbones"
            :key="`d-${idx}`"
            :transform="`translate(${c.x0} ${c.cy})`"
          >
            <line
              :x1="0"
              :y1="0"
              :x2="c.x1 - c.x0"
              :y2="0"
              :stroke="c.fill"
              :stroke-width="c.r"
              @mousedown="doStart($event, c, idx, 2)"
            ></line>
            <circle
              :r="c.r"
              :cx="0"
              :cy="0"
              :fill="c.fill"
              @mousedown="doStart($event, c, idx, 0)"
            ></circle>

            <circle
              :r="c.r"
              :cx="c.x1 - c.x0"
              :cy="0"
              :fill="c.fill"
              @mousedown="doStart($event, c, idx, 1)"
            ></circle>
            <g :transform="`matrix(1 0 0 -1 ${(c.x1 - c.x0) / 2} 24)`">
              <text :x="0" :y="0" style="font: 24px sans-serif;">
                {{ c.nm }}
              </text>
            </g>
          </g>
          <!--
            <path
              d="M 50 50 h 50 v 50 h -50 v-50"
              stroke="black"
              fill="transparent"
            ></path>
          -->
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
      offset: undefined,
      dogbones: [],
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
      this.dogbones.push({
        x0: 4 * this.step,
        x1: 8 * this.step,
        cy: (i + 4) * this.step,
        r: this.r,
        fill: '#ff0000',
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
          this.dogbones = response['data']
        })
        .catch(e => {
          this.errors.push(e)
        })
    },
    postContent: function() {
      axios
        .post('http://localhost:5000/post', this.dogbones, {
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
    doMove: function(event) {
      if (this.moving) {
        let dg = this.dogbones[this.moving_idx]
        /*
        s 0  0      1/s 0    0       1 0 0
        0 -s h      0   -1/s h/s  =  0 1 0
        0 0  1      0   0    1       0 0 1
        */
        // Hack to invert Y flip transformation
        let x = event.offsetX / this.scale
        let y = (this.height - event.offsetY) / this.scale

        if (this.code == 0) {
          dg.x0 = x
        } else if (this.code == 1) {
          dg.x1 = x
        } else if (this.code == 2) {
          let delta = dg.x1 - dg.x0
          dg.x0 = x - this.offset
          dg.x1 = dg.x0 + delta
          dg.cy = y
        }
      }
    },
    doStart: function(event, c, idx, code) {
      console.log('Start: ', event, c, idx, code)
      this.code = code
      this.moving = true
      this.moving_idx = idx
      let dg = this.dogbones[this.moving_idx]
      this.offset = event.offsetX / this.scale - dg.x0
    },
    doEnd: function() {
      if (this.moving) {
        const e = Elastic.easeOut.config(1, 0.3)
        const t = 0.5
        let dg = this.dogbones[this.moving_idx]

        if (this.code == 0) {
          let targetX0 = this.roundNearestGrid(dg.x0)
          TweenMax.to(dg, t, {
            x0: targetX0,
            ease: e
          })
        } else if (this.code == 1) {
          let targetX1 = this.roundNearestGrid(dg.x1)
          TweenMax.to(dg, t, {
            x1: targetX1,
            ease: e
          })
        } else if (this.code == 2) {
          let delta = dg.x1 - dg.x0
          let targetX0 = this.roundNearestGrid(dg.x0)
          let targetX1 = targetX0 + delta
          let targetCY = this.roundNearestGrid(dg.cy)
          TweenMax.to(dg, t, {
            x0: targetX0,
            x1: targetX1,
            cy: targetCY,
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
