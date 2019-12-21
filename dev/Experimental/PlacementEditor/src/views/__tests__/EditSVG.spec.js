import EditSVG from '@/views/EditSVG.vue'
import { shallowMount } from '@vue/test-utils'

describe('EditSVG.vue', () => {
  test('sanity test', () => {
    expect(true).toBe(true)
  })

  test('Renders load button', () => {
    const wrapper = shallowMount(EditSVG)
    expect(wrapper.text()).toContain('Load')
  })

  test('Renders save button', () => {
    const wrapper = shallowMount(EditSVG)
    expect(wrapper.text()).toContain('Save')
  })

  test('Checks stateless method: bboxToPath', () => {
    const wrapper = shallowMount(EditSVG)
    const result = wrapper.vm.bboxToPath([0, 1, 2, 3])
    expect(result).toContain('M 0 1 H 2 V 3 H 0 Z')
  })

  test('Checks stateful method: terminalLocation', () => {
    const wrapper = shallowMount(EditSVG)
    wrapper.vm.leaf_tbl = { leaf: { bbox: [0, 0, 4, 2] } }
    let c = {
      w: 100,
      h: 100,
      template_name: 'leaf',
      transformation: { oX: 0, oY: 0, sX: 1, sY: 1 }
    }
    let term = { rect: [1, 0, 3, 0] }
    expect(wrapper.vm.terminalLocation(c, term)).toEqual({
      x: 50,
      y: 0
    })
    term.rect[3] = 2
    expect(wrapper.vm.terminalLocation(c, term)).toEqual({
      x: 50,
      y: 50
    })
    c.transformation.oX = -50
    expect(wrapper.vm.terminalLocation(c, term)).toEqual({
      x: 0,
      y: 50
    })
    c.transformation.sX = -1
    expect(wrapper.vm.terminalLocation(c, term)).toEqual({
      x: -100,
      y: 50
    })
    c.transformation.sY = -1
    expect(wrapper.vm.terminalLocation(c, term)).toEqual({
      x: -100,
      y: -50
    })
    c.transformation.oY = 50
    expect(wrapper.vm.terminalLocation(c, term)).toEqual({
      x: -100,
      y: 0
    })
  })
})
