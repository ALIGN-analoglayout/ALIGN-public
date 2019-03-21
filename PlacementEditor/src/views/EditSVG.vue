<template>
  <div>
    <h1>SVG-Based Placement Editor/Visualizer</h1>
    <div class="container">
      <div class="row">
        <div class="col-sm-12">
          <vue-slider
            ref="slider"
            v-model="theta_timeline"
            :min="0"
            :max="leaves_array.length - 1"
            :width="'960px'"
            :interval="0.001"
            :speed="0"
          ></vue-slider>
        </div>
        <div class="col-sm-12">
          <vue-slider
            ref="scale_factor"
            v-model="scale_factor"
            :min="0.5"
            :max="8"
            :width="'960px'"
            :interval="0.001"
            :speed="0"
          ></vue-slider>
        </div>
        <div class="col-sm-12">
          <vue-slider
            ref="sch"
            v-model="sch"
            :min="1 - scale_factor"
            :max="1"
            :width="'960px'"
            :interval="0.001"
            :speed="0"
          ></vue-slider>
        </div>
        <div class="col-sm-12">
          <vue-slider
            ref="scv"
            v-model="scv"
            :min="1 - scale_factor"
            :max="1"
            :width="'960px'"
            :interval="0.001"
            :speed="0"
          ></vue-slider>
        </div>
      </div>
      <div class="row">
        <div class="col-sm-12">
          <div class="load-save-buttons">
            <button class="load-save-buttons" @click="getContent">Load</button>
            <button class="load-save-buttons" @click="postContent">Save</button>
            <label for="index">Index:</label>
            <input id="index" class="small-num" v-model="leaves_idx" />
            <button class="load-save-buttons" @click="animatePlacementChange">
              Animate
            </button>
            <span>{{ theta_rounded }}</span>
            <button class="load-save-buttons" @click="resetPlacementChange">
              Reset
            </button>
          </div>
          <!---
          <div class="value-tbl" v-for="(c, idx) in instances" :key="`i-${idx}`">
            <span class="value-span">{{ c.nm }}</span> <input v-model="c.w" />
            <input v-model="c.h" /> <input v-model="c.transformation.oX" />
            <input v-model="c.transformation.oY" />
            <input v-model="c.transformation.sX" />
            <input v-model="c.transformation.sY" />
          </div>
          --->
        </div>
      </div>
      <div class="row">
        <div class="col-sm-12">
          <svg
            :width="width"
            :height="height"
            @mousemove="doMove($event)"
            @mouseup="doEnd($event)"
          >
            <g
              :transform="
                `matrix(${scale} 0 0 ${-scale} ${sch * width} ${(1 - scv) *
                  height})`
              "
            >
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
                v-for="(c, idx) in instances"
                :key="`d-${idx}`"
                :transform="
                  `translate(${c.transformation.oX} ${
                    c.transformation.oY
                  }) scale(${c.transformation.sX} ${c.transformation.sY})`
                "
                @mousedown="doStart($event, c, idx, 2)"
              >
                <path
                  :d="`M 0 0 h ${c.w} v ${c.h} h ${-c.w} v ${-c.h}`"
                  stroke="black"
                  :fill="c.fill"
                ></path>
                <path
                  :d="`M 0 ${c.h / 5} L ${c.w / 5} 0`"
                  stroke="black"
                  stroke-width="2"
                  :fill="c.fill"
                ></path>
                <g :transform="`matrix(1 0 0 -1 0 ${c.h / 2})`">
                  <g transform="`matrix(1 0 0 1 0 0)`">
                    <text
                      :x="c.w / 2.0 - 60"
                      :y="100"
                      style="font: 36px sans-serif;"
                    >
                      {{ c.nm }}
                    </text>
                  </g>
                  <g
                    v-for="(term, idx1) in terminalList(c)"
                    :key="`t-${idx}-${idx1}`"
                    :transform="`matrix(0 -1 1 0 ${term.ox} ${term.oy})`"
                  >
                    <text :x="0" :y="0" style="font: 36px sans-serif;">
                      {{ term.nm }}
                    </text>
                  </g>
                </g>
              </g>
            </g>
          </svg>
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import {
  Elastic,
  /*SlowMo, SteppedEase, Power0,*/
  Power2,
  /*TweenMax,*/
  TweenLite,
  TimelineLite
} from 'gsap'

import vueSlider from 'vue-slider-component'
export default {
  components: {
    vueSlider
  },
  data: function() {
    const width = 960
    const height = 960

    return {
      width: width,
      height: height,
      stepx: undefined,
      stepy: undefined,
      ny: undefined,
      nx: undefined,
      moving: false,
      moving_idx: undefined,
      code: undefined,
      offx: undefined,
      offy: undefined,
      leaves_array: [],
      hgridlines: [],
      vgridlines: [],
      errors: [],
      leaves_idx: 0,
      theta: 0.0,
      theta_percent: 0,
      scale_factor: 1,
      sch: 0,
      scv: 0
    }
  },
  computed: {
    scale: function() {
      if (
        this.stepy * this.ny * this.width >
        this.stepx * this.nx * this.height
      ) {
        // ny is constraining
        return (this.scale_factor * this.height) / (this.ny * this.stepy)
      } else {
        return (this.scale_factor * this.width) / (this.nx * this.stepx)
      }
    },
    theta_timeline: {
      get: function() {
        return this.theta + this.leaves_idx
      },
      set: function(val) {
        this.leaves_idx = Math.trunc(val)
        this.theta = val - this.leaves_idx
      }
    },
    leaves_idx_next: function() {
      return this.leaves_idx + 1
    },
    theta_rounded: function() {
      return this.theta.toFixed(3)
    },
    instances: function() {
      let sArray = this.leaves_array[this.leaves_idx]
      if (this.theta == 0) {
        return sArray // if we aren't animating, then the first element.
      }
      let cArray = sArray.map(a => ({ ...a }))
      let eArray = this.leaves_array[this.leaves_idx_next]
      for (let i = 0; i < sArray.length; i += 1) {
        let cTrans = { ...cArray[i].transformation }
        let sTrans = sArray[i].transformation
        let eTrans = eArray[i].transformation
        let b = this.theta
        let a = 1 - this.theta

        cTrans.oX = a * sTrans.oX + b * eTrans.oX
        cTrans.oY = a * sTrans.oY + b * eTrans.oY
        cTrans.sX = a * sTrans.sX + b * eTrans.sX
        cTrans.sY = a * sTrans.sY + b * eTrans.sY

        cArray[i].transformation = cTrans
      }

      return cArray
    }
  },
  methods: {
    terminalList: function(c) {
      if (this.hasOwnProperty('leaf_templates')) {
        var leaf = this.leaf_tbl[c.template_name]
        var result = leaf.terminals.map(function(term) {
          var actual = c.hasOwnProperty('formal_actual_map')
            ? c.formal_actual_map[term.net_nm]
            : 'no_map'
          var shift = 25
          var ox =
            1.5 * shift + ((-2 * shift + c.w) * term.rect[0]) / leaf.bbox[2]
          return { nm: actual, ox: ox, oy: 0 }
        })
        console.log(result)
        return result
      } else {
        return []
      }
    },
    setupGridlines: function() {
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
    resetPlacementChange: function() {
      this.theta = 0.0
      this.leaves_idx = 0
      this.scale_factor = 1
      this.sch = 0
      this.scv = 0
    },
    animatePlacementChange: function() {
      //const e = Elastic.easeOut.config(1, 0.3)
      //const e = SlowMo.ease.config(0.7, 0.7, false)
      //const e = SteppedEase.ease.config(10)
      //const e = Power0.easeNone
      const e = Power2.easeInOut
      const t = 1.0
      var tl = new TimelineLite()
      console.log(this.leaves_array.length)
      for (let i = 0; i < this.leaves_array.length - 1; i += 1) {
        console.log('Setting up:', i)
        tl.set(this, { theta: 0, leaves_idx: i, leaves_idx_next: i + 1 })
        tl.to(this, t, {
          theta: 1.0,
          ease: e
        })
      }
    },
    getContent: function() {
      axios
        .get('http://localhost:5000/get')
        .then(response => {
          let r = response['data']
          this.leaves_array = r['placements_for_animation']
          this.nx = r['nx']
          this.ny = r['ny']
          this.stepx = r['stepx']
          this.stepy = r['stepy']
          this.leaf_templates = r['leaves']
          this.leaf_tbl = {}
          for (let i = 0; i < this.leaf_templates.length; i += 1) {
            this.leaf_tbl[
              this.leaf_templates[i].template_name
            ] = this.leaf_templates[i]
          }
          console.log(this.leaf_templates)
          this.setupGridlines()
        })
        .catch(e => {
          this.errors.push(e)
        })
    },
    postContent: function() {
      let r = {
        placements_for_animation: this.leaves_array,
        nx: this.nx,
        ny: this.ny,
        stepx: this.stepx,
        stepy: this.stepy,
        leaves: this.leaf_templates
      }
      axios
        .post('http://localhost:5000/post', r, {
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
        let dg = this.instances[this.moving_idx]
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
      let dg = this.instances[this.moving_idx]
      this.offx = this.getEventX(event) - dg.transformation.oX
      this.offy = this.getEventY(event) - dg.transformation.oY
    },
    doEnd: function() {
      if (this.moving) {
        const e = Elastic.easeOut.config(1, 0.3)
        const t = 0.5
        let dg = this.instances[this.moving_idx]

        if (this.code == 2) {
          let targetX = this.roundNearestGridX(dg.transformation.oX)
          let targetY = this.roundNearestGridY(dg.transformation.oY)
          TweenLite.to(dg.transformation, t, {
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

<style scoped>
.value-tbl > input {
  font-family: monospace;
  font-size: 12pt;
  width: 8ex;
  text-align: right;
  /*border-radius: 10pt;*/
}
.value-span {
  font-family: monospace;
  padding: 2pt;

  display: inline-block;
  font-size: 12pt;
  width: 8ex;
  text-align: left;
  border: 0.5px solid gray;
}
.load-save-buttons {
  padding: 5pt;
  border-radius: 5pt;
}
.load-save-buttons > input {
  width: 6ex;
}
.small-num {
  padding: 5pt;
  font-family: monospace;
  width: 3ex;
  text-align: right;
}
</style>
