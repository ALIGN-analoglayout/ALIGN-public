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
})
