mw = RBA::Application::instance.main_window
mw.load_layout($infile, 1)

view = mw.current_view
view.max_hier
view.zoom_fit

view.save_image($outfile, 8 * view.viewport_width, 8 * view.viewport_height)

