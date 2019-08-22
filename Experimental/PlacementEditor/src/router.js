import Vue from 'vue'
import Router from 'vue-router'
import EditSVG from './views/EditSVG.vue'

Vue.use(Router)

export default new Router({
  mode: 'history',
  base: process.env.BASE_URL,
  routes: [
    {
      path: '/',
      name: 'edit-svg',
      component: EditSVG
    }
  ]
})
