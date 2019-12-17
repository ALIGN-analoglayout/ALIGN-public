#!/usr/bin/python3

import random
#import os
import sys

class Read_Write_File:
  def __init__(self,ReadFile_name):
    self.read_file_name = ReadFile_name
    self.write_file_name = ReadFile_name+'_bk'
  def Read_Write(self):
    fin = open(self.read_file_name,'r')
    spfile = fin.readlines()
    fout = open(self.write_file_name, "w")
    for lines in spfile:
      words = lines.split()
      for word in words:
        if word.find('nfin')==-1:
          fout.write(word)
          fout.write(' ')
        else:
          #L = random.uniform(10,500) # a random number if need recover this line
          L = 50
          fout.write('nfin='+str(L))
          fout.write(' ')
      fout.write('\n')
    fout.close()

def main(file_name):
  read_write = Read_Write_File(file_name)
  read_write.Read_Write()

if __name__ == '__main__':
  string = sys.argv[1]
  main(string)             
