import Vue from 'vue'
import Router from 'vue-router'
import EventSVG from './views/EventSVG.vue'

Vue.use(Router)

export default new Router({
  mode: 'history',
  base: process.env.BASE_URL,
  routes: [
    {
      path: '/',
      name: 'event-svg',
      component: EventSVG
    }
  ]
})
