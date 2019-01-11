import gdswriter

w = gdswriter.PyGdsWriter(b"xxx.gds")
w.create_lib(b"foo",1,1)
print( w.__dir__())
