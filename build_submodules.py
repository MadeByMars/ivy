import sys
import os
import platform
if platform.system() == 'Windows':
    print "windows build is not currently supported"
    exit(1)

so_ext = "so"
if platform.system() == 'Darwin':
    so_ext = "dylib"

def do_cmd(cmd):
    print cmd
    status = os.system(cmd)
    if status:
        exit(1)
    
cwd = os.getcwd()

if not os.path.exists('submodules/z3'):
    print "submodules/z3 not found. try 'git submodule update; git submodule update'"
    exit(1)

os.chdir('submodules/z3')

ivydir = os.path.join(cwd,'ivy')

cmd = 'python scripts/mk_make.py --python --prefix {} --pypkgdir {}/'.format(cwd,ivydir)

do_cmd(cmd)

os.chdir('build')

do_cmd('make -j 4')

do_cmd('rm -f {}/z3/lib/libz3.{}'.format(ivydir,so_ext)) # work around Z3 install bug

do_cmd('make install')

os.chdir(cwd)

if not os.path.exists('ivy/lib'):
    do_cmd('mkdir ivy/lib')

do_cmd('cp include/*.h ivy/include')
do_cmd('cp lib/*.{} ivy/lib'.format(so_ext))
do_cmd('cp lib/*.{} ivy/z3'.format(so_ext))


if not os.path.exists('submodules/picotls'):
    print "submodules/picotls not found. try 'git submodule update; git submodule update'"
    exit(1)

os.chdir('submodules/picotls')

do_cmd('git submodule init')
do_cmd('git submodule update')
do_cmd('cmake .')
do_cmd('make')
do_cmd('cp -a include/*.h include/picotls ../../ivy/include/')
do_cmd('cp -a *.a ../../ivy/lib/')

