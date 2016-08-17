#include <string.h>
#include <stdio.h>

#include "universe.h"
#include "readwrite.h"


int read_life105(FILE *f, 
                 void (*cb)(void *, char, int, int, int, char), 
                 void (*paramcb)(void *, const char *, const char *),
                 void *cbdata) {

        char linebuff[10000];        
        char parambuff[63 + 1];
        char valuebuff[63 + 1];
        int gen, xpos, ypos;
        char area = 'P';

        while(fgets(linebuff, sizeof linebuff, f)) {
                char *p = strchr(linebuff, '\r');
                if(p) *p = 0;
                p = strchr(linebuff, '\n');
                if(p) *p = 0;

                if(linebuff[0] == '#') switch(linebuff[1]) {
                        
                case 'L':
                        // version header; ignore
                        break;

                case 'D': 
                        // description; ignore
                        break;

                case 'C': 
                        // comment; ignore
                        break;

                case 'N':
                        // use normal Life rules
                        break;

                case 'P':
                        // set co-ordinates
                        area = 'P';
                        gen = 0;
                        if(sscanf(linebuff + 2, "%d %d", &xpos, &ypos) != 2) {
                                fprintf(stderr, "Bad pattern header: '%s'\n", linebuff);
                                return 0;
                        }
                        break;

                case 'F':
                        // set co-ordinates
                        area = 'F';
                        if(sscanf(linebuff + 2, "%d %d %d", &gen, &xpos, &ypos) != 3) {
                                fprintf(stderr, "Bad filter header: '%s'\n", linebuff);
                                return 0;
                        }
                        break;

                case 'S':
                        // search space control parameter
                        if(sscanf(linebuff + 2, "%63s %63s", parambuff, valuebuff) != 2) {
                                fprintf(stderr, "Bad search parameter line: '%s'\n", linebuff);
                                return 0;
                        }
                        if(paramcb)
                                paramcb(cbdata, parambuff, valuebuff);
                        break;

                default:
                        fprintf(stderr, "--- Unknown line: '%s'\n", linebuff);
                        break;

                } else {
                        // Process as data.
                        int x = xpos;

                        for(p = linebuff; *p; p++) {
                                cb(cbdata, area, gen, x, ypos, *p);
                                x++;
                        }
                        ypos++;
                }
        }
		
		return 1;
}

static void life105cb(void *u_, char area, int gen, int x, int y, char c) {
        universe *u = (universe *)u_;
        cellvalue v = OFF;
        if((area == 'P') && (gen == 0)) {
                switch(c) {
                case '.': v = OFF; break;
                case '*': v = ON;  break;
                case '?': v = UNKNOWN_STABLE; break;
                case '@': v = UNKNOWN; break;
                }
                generation_set_cell(u->first, x, y, v);
        }
}

static void read_rle(FILE *f, universe *u) {
        char linebuff[10000];        
        int xpos = 0, ypos = 0;

        // read header lines

        while(fgets(linebuff, sizeof linebuff, f)) {
                if(!strncmp(linebuff, "x = ", 4)) {
                        if(linebuff[0] == '#') {
                                fprintf(stderr, "%s\n", linebuff);
                        } else if(sscanf(linebuff, "x = %d, y = %d", &xpos, &ypos) == 2) {
                                break;
                        }
                }
        }

        // read data
        int xcur = xpos;
        int count = 0;

        while(fgets(linebuff, sizeof linebuff, f)) {
                char *p = linebuff;

                while(*p) {
                        if((*p >= '0') && (*p <= '9')) {
                                count = (count * 10) + (*p - '0');

                        } else if(*p == 'b') {

                                if(count == 0)
                                        count = 1;
                                while(count--) {
                                        generation_set_cell(u->first, xcur++, ypos, OFF);
                                }
                                count = 0;

                        } else if(*p == 'o') {

                                if(count == 0)
                                        count = 1;
                                while(count--)
                                        generation_set_cell(u->first, xcur++, ypos, ON);
                                count = 0;

                        } else if(*p == '$') {

                                if(count == 0)
                                        count = 1;
                                while(count--) {
                                        ypos++;
                                        xcur = xpos;
                                }
                                count = 0;

                        } else if(*p == '\n') {

                                // ignore

                        } else if(*p == '!') {

                                return;

                        } else {
                                fprintf(stderr, "Bad char '%c' in RLE\n", *p);
                        }
                        p++;
                }
        }
}

universe *read_text(const char *filename) {
        char firstline[1000];

        FILE *f = fopen(filename, "r");
        if(!f) {
                perror(filename);
                return NULL;
        }

        universe *u = universe_new(OFF);

        if(fgets(firstline, sizeof firstline, f) == NULL) {
                perror(filename);
                fclose(f);
                return NULL;
        }

        fseek(f, 0, SEEK_SET);

        if(!strncmp(firstline, "#CXRLE ", 7)) {

                read_rle(f, u);

        } else if((firstline[0] == '#') &&
                  (firstline[1] != 0) &&
                  (firstline[2] == ' ')) {

                read_life105(f, life105cb, NULL, u);

        } else {
                fprintf(stderr, "Unknown format '%s'\n", firstline);
                fclose(f);
                return NULL;
        }

        fclose(f);

        return u;
}

