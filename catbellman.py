import os, glob
import golly as g

def convbellman (text, stx, sty):
	textln = text.split ('\n')
	
	gen = -1
	y = sty;
	for ln in textln:
		if not ln:
			break
		if ln [0] == '#':
			if ln [0:35] == "#C Solution accepted at generation ":
				gen = int (ln [35:])
		else:
			x = stx;
			for c in ln:
				if c == '.':
					g.setcell (x, y, 0)
					x += 1;
				elif c == '?':
					g.setcell (x, y, 5)
					x += 1;
				elif c == '*':
					g.setcell (x, y, 3)
					x += 1;
				elif c == '@':
					g.setcell (x, y, 1)
					x += 1;
			y += 1
	return gen

def clean (rect):
  for y in xrange (rect [1], rect [1] + rect [3]):
    for x in xrange (rect [0], rect [0] + rect [2]):
      if g.getcell (x, y) != 1:
        g.setcell (x, y, 0)

def addmarkers (rect):
  g.setcell (rect [0], rect [1], 1)
  g.setcell (rect [0] + rect [2] - 1, rect [1], 1)
  g.setcell (rect [0], rect [1] + rect [3] - 1, 1)
  g.setcell (rect [0] + rect [2] - 1, rect [1] + rect [3] - 1, 1)

def analyse (gogen, minpop, maxpop, needgl):
  g.run (gogen)
  inrect = g.getrect ()
  clean (inrect)

  endpop = int (g.getpop ())
  if endpop < minpop or endpop > maxpop:
    return (False, 0)

  rect = g.getrect ()
  if rect == []:
    return (True, 0)
  else:
    if needgl:
      g.run (4)
      newrect = g.getrect ()
      clean (newrect)
      newrect = g.getrect ()
      if newrect == rect:
        return (False, 0)

    addmarkers (inrect)
    return (True, g.hash (inrect))

def main ():
  g.update ()
  g.check (False)

  path = g.getstring ("Output directory:")
  files = glob.glob (os.path.join (path, "*.out"))

  minpops = g.getstring ("Min population except catalyzers:")
  if minpops == "":
    minpop = 0
    maxpop = 1024
    needgl = False
  else:
    minpop = int (minpops)
    maxpop = int (g.getstring ("Max population except catalyzers:"))
    ngl = g.getstring ("Require at least one escaping glider (y/n):")
    needgl = ngl == 'y'

  if g.getname () != "catbellman_temp":
    g.addlayer ()

  hashdir = {}
  catlist = []
  catix = 0

  g.new ("catbellman_temp")
  g.setrule ("LifeBellman")

  for fix, filename in enumerate (files):
    patt = g.getrect ()
    if patt != []:
      g.select (patt)
      g.clear (0)
  
    g.setgen ("0")
	
    with open(filename, 'r') as f:
      filetext = f.read ()
      if fix % 16 == 0:
        g.show ("Analysing " + str (fix) + "/" + str (len (files)))
		
      gogen = convbellman (filetext, 0, 0)
      if gogen == -1:
	    gogen = 128
	  
      (use, hash) = analyse (gogen, minpop, maxpop, needgl)

      if use:
        if not hash in hashdir:
          catlist.append ([])
          hashdir [hash] = catix
          catix += 1

        cat = hashdir [hash]
        catlist [cat].append (filetext)

  g.new ("catbellman_temp")
  g.setrule ("LifeBellman")

  fix = 0
  y = 0
  for cat in catlist:
    x = 96 * (len (cat) - 1)
    for filetext in cat:
      convbellman (filetext, x, y)
      x -= 96
      fix += 1
      if fix % 32 == 0:
        g.show ("Rendering " + str (fix) + "/" + str (len (files)))
        g.fit ()
        g.check (True)
        g.update ()
        g.check (False)

    y += 96

  g.show ("Done")
  g.fit ()
  g.setstep (-1)
  g.check (True)

main ()
