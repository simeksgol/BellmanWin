#include <assert.h>
#include "universe.h"
#include "bitwise.h"

evolve_result tile_evolve_bitwise(tile *t, tile *out) {
        evolve_result flags = 0;

        int y;

        TILE_WORD up_left, up, up_right;
        tile *t_up = t->up;

        if(t_up) {
                up = t_up->bit0[TILE_HEIGHT-1];
                up_left = get_word0_left(t_up, TILE_HEIGHT-1);
                up_right = get_word0_right(t_up, TILE_HEIGHT-1);

        } else up_left = up = up_right = 0;

        TILE_WORD mid_left, mid, mid_right;

        mid = t->bit0[0];
        mid_left = get_word0_left(t, 0);
        mid_right = get_word0_right(t, 0);

        if(mid != 0) flags |= EXPAND_UP;

        TILE_WORD down_left, down, down_right;

        TILE_WORD left_expand_flag = 0, right_expand_flag = 0;
        TILE_WORD any_active = 0;
        // full adders to count the live bits on each row
        full_adder(uptotal, up_total0, up_total1, up_left, up, up_right);
        full_adder(midtotal, mid_total0, mid_total1, mid_left, mid, mid_right);

        for(y=0; y<TILE_HEIGHT; y++) {
                if(y == TILE_HEIGHT-1) {
                        if(t->down) {
                                down = t->down->bit0[0];
                                down_left = get_word0_left(t->down, 0);
                                down_right = get_word0_right(t->down, 0);
                        } else down_left = down = down_right = 0;
                } else {
                        down = t->bit0[y + 1];
                        down_left = get_word0_left(t, y + 1);
                        down_right = get_word0_right(t, y + 1);
                }

                left_expand_flag |= mid & 1;
                right_expand_flag |= mid & (((TILE_WORD)1) << (TILE_WIDTH-1));

                full_adder(downtotal, down_total0, down_total1, down_left, down, down_right);

                // now add together the up and mid sums
                half_adder(    upmid_total0, upmid_carry0, up_total0, mid_total0);
                full_adder(t1, upmid_total1, upmid_total2, up_total1, mid_total1, upmid_carry0);

                // now add the down sum
                half_adder(    neigh_total0, neigh_carry0, upmid_total0, down_total0);
                full_adder(t2, neigh_total1, neigh_carry1, upmid_total1, down_total1, neigh_carry0);
                half_adder(    neigh_total2, neigh_total3, upmid_total2, neigh_carry1);

                // Now implement the Life rule. The result is on if
                // the cell is on and has 2 or 3 neighbours, or if the
                // cell is off and has 3 neighbours. However we have
                // included the cell itself in the neighbour total, so
                // the actual values we're looking for are:
                //
                // c=0:  0, 0, 1, 1
                // c=1:  0, 0, 1, 1
                // c=1:  0, 1, 0, 0

                // If the count is 3 then the cell is live

                TILE_WORD is_live = (~neigh_total3) & (~neigh_total2) & neigh_total1 & neigh_total0;

                // For a live cell, we accept c=4 too.
                is_live |= mid & ((~neigh_total3) & neigh_total2 & (~neigh_total1) & (~neigh_total0));

                // We have our result!
                out->bit0[y] = is_live;
                any_active |= is_live;

                // Shift the previous results
                up_total0 = mid_total0; up_total1 = mid_total1;
                mid_total0 = down_total0; mid_total1 = down_total1;
                up = mid; mid = down;
        }

        if(any_active == 0) flags |= IS_DEAD;
        if(left_expand_flag != 0) flags |= EXPAND_LEFT;
        if(right_expand_flag != 0) flags |= EXPAND_RIGHT;
        if(up != 0) flags |= EXPAND_DOWN;

        return flags;
}

evolve_result tile_evolve_bitwise_3state(tile *t, tile *out) {
        evolve_result flags = 0;

        int y;

        TILE_WORD up_left, up, up_right;
        TILE_WORD up_unk_left, up_unk, up_unk_right;
        tile *t_up = t->up;

        if(t_up) {
                GET3WORDS(up_left, up, up_right, t_up, 0, TILE_HEIGHT-1);
                GET3WORDS(up_unk_left, up_unk, up_unk_right, t_up, 1, TILE_HEIGHT-1);
                
                // map 11 -> 10
                up_left &= ~up_unk_left;
                up &= ~up_unk;
                up_right &= ~up_unk_right;
        } else up_left = up = up_right = up_unk_left = up_unk = up_unk_right = 0;

        TILE_WORD mid_left, mid, mid_right;
        TILE_WORD mid_unk_left, mid_unk, mid_unk_right;

        GET3WORDS(mid_left, mid, mid_right, t, 0, 0);
        GET3WORDS(mid_unk_left, mid_unk, mid_unk_right, t, 1, 0);

        // map 11 -> 10
        mid_left &= ~mid_unk_left;
        mid &= ~mid_unk;
        mid_right &= ~mid_unk_right;

        if((mid != 0) || (mid_unk != 0)) flags |= EXPAND_UP;

        TILE_WORD down_left, down, down_right;
        TILE_WORD down_unk_left, down_unk, down_unk_right;

        TILE_WORD left_expand_flag = 0, right_expand_flag = 0;
        TILE_WORD any_active = 0;
        // full adders to count the live bits on each row
        full_adder(uptotal, up_total0, up_total1, up_left, up, up_right);
        full_adder(midtotal, mid_total0, mid_total1, mid_left, mid, mid_right);
        // and the unknown bits
        full_adder(uputotal, up_unk_total0, up_unk_total1, up_unk_left, up_unk, up_unk_right);
        full_adder(midutotal, mid_unk_total0, mid_unk_total1, mid_unk_left, mid_unk, mid_unk_right);

        TILE_WORD top_delta = 0, bottom_delta = 0, all_delta = 0;

        for(y=0; y<TILE_HEIGHT; y++) {
                if(y == TILE_HEIGHT-1) {
                        if(t->down) {
                                GET3WORDS(down_left, down, down_right, t->down, 0, 0);
                                GET3WORDS(down_unk_left, down_unk, down_unk_right, t->down, 1, 0);
                        } else down_left = down = down_right = down_unk_left = down_unk = down_unk_right = 0;
                } else {
                        GET3WORDS(down_left, down, down_right, t, 0, y + 1);
                        GET3WORDS(down_unk_left, down_unk, down_unk_right, t, 1, y + 1);
                }

                // map 11 -> 10
                down_left &= ~down_unk_left;
                down &= ~down_unk;
                down_right &= ~down_unk_right;

                left_expand_flag |= (mid | mid_unk) & 1;
                right_expand_flag |= (mid | mid_unk) & (((TILE_WORD)1) << (TILE_WIDTH-1));

                full_adder(downtotal, down_total0, down_total1, down_left, down, down_right);
                full_adder(downutotal, down_unk_total0, down_unk_total1, down_unk_left, down_unk, down_unk_right);

                // now add together the up and mid sums
                half_adder(    upmid_total0, upmid_carry0, up_total0, mid_total0);
                full_adder(t1, upmid_total1, upmid_total2, up_total1, mid_total1, upmid_carry0);

                half_adder(     upmid_unk_total0, upmid_unk_carry0, up_unk_total0, mid_unk_total0);
                full_adder(t1u, upmid_unk_total1, upmid_unk_total2, up_unk_total1, mid_unk_total1, upmid_unk_carry0);

                // now add the down sum
                half_adder(    neigh_total0, neigh_carry0, upmid_total0, down_total0);
                full_adder(t2, neigh_total1, neigh_carry1, upmid_total1, down_total1, neigh_carry0);
                half_adder(    neigh_total2, neigh_total3, upmid_total2, neigh_carry1);

                half_adder(     neigh_unk_total0, neigh_unk_carry0, upmid_unk_total0, down_unk_total0);
                full_adder(t2u, neigh_unk_total1, neigh_unk_carry1, upmid_unk_total1, down_unk_total1, neigh_unk_carry0);
                half_adder(     neigh_unk_total2, neigh_unk_total3, upmid_unk_total2, neigh_unk_carry1);

                (void)neigh_total3;

                // Now implement the 3-state Life rule, remembering
                // that we've included the cell itself in the counts.

                TILE_WORD is_live = 0, is_unk = 0;

                // code generated by mkrule.py...
is_unk |= neigh_unk_total3 ;
is_unk |= (~neigh_total2) & neigh_unk_total2 ;
is_unk |= mid & (~neigh_total0) & neigh_unk_total2 ;
is_unk |= (~neigh_total2) & neigh_total1 & neigh_unk_total1 ;
is_unk |= (~neigh_total2) & neigh_total0 & neigh_unk_total1 ;
is_unk |= (~neigh_total2) & neigh_unk_total1 & neigh_unk_total0 ;
is_unk |= mid & (~neigh_total1) & (~neigh_total0) & neigh_unk_total1 ;
is_unk |= (~mid_unk) & (~mid) & (~neigh_total2) & neigh_total1 & neigh_unk_total0 ;
is_live |= mid_unk & (~neigh_total2) & neigh_total1 & neigh_total0 & (~neigh_unk_total2) & (~neigh_unk_total1) ;
is_live |= mid & (~neigh_total2) & neigh_total1 & neigh_total0 & (~neigh_unk_total2) & (~neigh_unk_total1) ;
is_live |= (~neigh_total2) & neigh_total1 & neigh_total0 & (~neigh_unk_total2) & (~neigh_unk_total1) & (~neigh_unk_total0) ;
is_unk |= (~neigh_total2) & neigh_total1 & (~neigh_total0) & neigh_unk_total0 ;
is_unk |= mid & neigh_total2 & (~neigh_total1) & (~neigh_total0) & neigh_unk_total0 ;
is_live |= mid & neigh_total2 & (~neigh_total1) & (~neigh_total0) & (~neigh_unk_total2) & (~neigh_unk_total1) & (~neigh_unk_total0) ;

#if 0
                int x;
                for(x=0; x<TILE_WIDTH; x++) {
                        int cb0 = (neigh_total0 >> x) & 1;
                        int cb1 = (neigh_total1 >> x) & 1;
                        int cb2 = (neigh_total2 >> x) & 1;
                        int cb3 = (neigh_total3 >> x) & 1;
                        int ub0 = (neigh_unk_total0 >> x) & 1;
                        int ub1 = (neigh_unk_total1 >> x) & 1;
                        int ub2 = (neigh_unk_total2 >> x) & 1;
                        int ub3 = (neigh_unk_total3 >> x) & 1;
                        int v = (mid >> x) & 1;
                        v += ((mid_unk >> x) & 1) << 1;
                        int nv = (is_live >> x) & 1;
                        nv += ((is_unk >> x) & 1) << 1;
                        printf("%d, %d: v=%d, count=%d, unk=%d, new=%d\n",
                               x, y, v, (cb3 * 8) + (cb2 * 4) + (cb1 * 2) + cb0,
                               (ub3 * 8) + (ub2 * 4) + (ub1 * 2) + ub0, nv);

                }
#endif

                // We have our result!
                TILE_WORD delta = (out->bit0[y] ^ is_live) | (out->bit1[y] ^ is_unk);
                out->bit0[y] = is_live;
                out->bit1[y] = is_unk;
                any_active |= is_live | is_unk;

                // TODO: is this a branch or a CMOV?
                top_delta = (y == 0) ? delta : top_delta;
                bottom_delta = (y == (TILE_HEIGHT-1)) ? delta : bottom_delta;

                all_delta |= delta;

                // Shift the previous results
                up_total0 = mid_total0; up_total1 = mid_total1;
                mid_total0 = down_total0; mid_total1 = down_total1;
                up = mid; mid = down;

                up_unk_total0 = mid_unk_total0; up_unk_total1 = mid_unk_total1;
                mid_unk_total0 = down_unk_total0; mid_unk_total1 = down_unk_total1;
                up_unk = mid_unk; mid_unk = down_unk;
        }

        if(any_active == 0) flags |= IS_DEAD;
        if(left_expand_flag != 0) flags |= EXPAND_LEFT;
        if(right_expand_flag != 0) flags |= EXPAND_RIGHT;
        if((up | up_unk) != 0) flags |= EXPAND_DOWN;

        if(all_delta |= 0) flags |= CHANGED;
        if(top_delta != 0) flags |= EXPAND_UP;
        if(bottom_delta != 0) flags |= EXPAND_DOWN;
        if(all_delta & 1) flags |= EXPAND_LEFT;
        if(all_delta & (((TILE_WORD)1) << (TILE_WIDTH-1))) flags |= EXPAND_RIGHT;

        return flags;
}

evolve_result tile_stabilise_3state(tile *t, tile *out) {
        evolve_result flags = 0;

        int y;

        TILE_WORD up_left, up, up_right;
        TILE_WORD up_unk_left, up_unk, up_unk_right;
        tile *t_up = t->up;

        if(t_up) {
                GET3WORDS(up_left, up, up_right, t_up, 0, TILE_HEIGHT-1);
                GET3WORDS(up_unk_left, up_unk, up_unk_right, t_up, 1, TILE_HEIGHT-1);
                
                // map 11 -> 10
                up_left &= ~up_unk_left;
                up &= ~up_unk;
                up_right &= ~up_unk_right;
        } else up_left = up = up_right = up_unk_left = up_unk = up_unk_right = 0;

        TILE_WORD mid_left, mid, mid_right;
        TILE_WORD mid_unk_left, mid_unk, mid_unk_right;

        GET3WORDS(mid_left, mid, mid_right, t, 0, 0);
        GET3WORDS(mid_unk_left, mid_unk, mid_unk_right, t, 1, 0);

        // map 11 -> 10
        mid_left &= ~mid_unk_left;
        mid &= ~mid_unk;
        mid_right &= ~mid_unk_right;

        TILE_WORD down_left, down, down_right;
        TILE_WORD down_unk_left, down_unk, down_unk_right;

        TILE_WORD any_active = 0, abort = 0;
        // full adders to count the live bits on each row
        full_adder(uptotal, up_total0, up_total1, up_left, up, up_right);
        full_adder(midtotal, mid_total0, mid_total1, mid_left, mid, mid_right);
        // and the unknown bits
        full_adder(uputotal, up_unk_total0, up_unk_total1, up_unk_left, up_unk, up_unk_right);
        full_adder(midutotal, mid_unk_total0, mid_unk_total1, mid_unk_left, mid_unk, mid_unk_right);
		
        for(y=0; y<TILE_HEIGHT; y++) {
                if(y == TILE_HEIGHT-1) {
                        if(t->down) {
                                GET3WORDS(down_left, down, down_right, t->down, 0, 0);
                                GET3WORDS(down_unk_left, down_unk, down_unk_right, t->down, 1, 0);
                        } else down_left = down = down_right = down_unk_left = down_unk = down_unk_right = 0;
                } else {
                        GET3WORDS(down_left, down, down_right, t, 0, y + 1);
                        GET3WORDS(down_unk_left, down_unk, down_unk_right, t, 1, y + 1);
                }

                // map 11 -> 10
                down_left &= ~down_unk_left;
                down &= ~down_unk;
                down_right &= ~down_unk_right;

                full_adder(downtotal, down_total0, down_total1, down_left, down, down_right);
                full_adder(downutotal, down_unk_total0, down_unk_total1, down_unk_left, down_unk, down_unk_right);

                // now add together the up and mid sums
                half_adder(    upmid_total0, upmid_carry0, up_total0, mid_total0);
                full_adder(t1, upmid_total1, upmid_total2, up_total1, mid_total1, upmid_carry0);

                half_adder(     upmid_unk_total0, upmid_unk_carry0, up_unk_total0, mid_unk_total0);
                full_adder(t1u, upmid_unk_total1, upmid_unk_total2, up_unk_total1, mid_unk_total1, upmid_unk_carry0);

                // now add the down sum
                half_adder(    neigh_total0, neigh_carry0, upmid_total0, down_total0);
                full_adder(t2, neigh_total1, neigh_carry1, upmid_total1, down_total1, neigh_carry0);
                half_adder(    neigh_total2, neigh_total3, upmid_total2, neigh_carry1);

                half_adder(     neigh_unk_total0, neigh_unk_carry0, upmid_unk_total0, down_unk_total0);
                full_adder(t2u, neigh_unk_total1, neigh_unk_carry1, upmid_unk_total1, down_unk_total1, neigh_unk_carry0);
                half_adder(     neigh_unk_total2, neigh_unk_total3, upmid_unk_total2, neigh_unk_carry1);


                // Now implement the stabiliser rule.

                TILE_WORD is_live = 0, is_unk = 0;

                // code generated by mkrule.py...
abort |= (~mid) & (~neigh_total2) & neigh_total1 & neigh_total0 & (~neigh_unk_total2) & (~neigh_unk_total1) & (~neigh_unk_total0) ;
abort |= mid & (~neigh_total2) & (~neigh_total1) & (~neigh_unk_total3) & (~neigh_unk_total2) & (~neigh_unk_total1) ;
abort |= mid & (~neigh_total2) & (~neigh_total0) & (~neigh_unk_total2) & (~neigh_unk_total1) & (~neigh_unk_total0) ;
is_live |= mid & (~neigh_total3) & (~neigh_total2) & (~neigh_total0) & neigh_unk_total0 ;
is_live |= mid & neigh_total2 & (~neigh_total1) & (~neigh_total0) ;
is_unk |= mid_unk & (~neigh_total2) & neigh_total1 & (~neigh_total0) ;
is_unk |= mid_unk & (~neigh_total2) & neigh_unk_total1 & neigh_unk_total0 ;
is_live |= mid_unk & (~neigh_total2) & neigh_unk_total1 & neigh_unk_total0 ;
abort |= mid & neigh_total2 & neigh_total0 ;
abort |= mid & neigh_total2 & neigh_total1 ;
is_live |= mid & (~neigh_total2) & neigh_total1 & neigh_total0 ;
is_unk |= mid_unk & (~neigh_total2) & neigh_total0 & (~neigh_unk_total0) ;
is_live |= mid_unk & (~neigh_total2) & neigh_total0 & (~neigh_unk_total0) ;
is_live |= mid & (~neigh_total2) & neigh_unk_total1 ;
is_live |= mid & (~neigh_total2) & neigh_unk_total2 ;
is_live |= mid_unk & (~neigh_total2) & neigh_total1 ;
is_live |= neigh_total0 & neigh_unk_total3 ;
is_unk |= mid_unk & (~neigh_total2) & neigh_unk_total2 ;
is_live |= mid_unk & (~neigh_total2) & neigh_unk_total2 ;
is_unk |= mid_unk & neigh_unk_total3 ;
is_live |= mid_unk & neigh_unk_total3 ;

#if 0
                int x;
                for(x=0; x<TILE_WIDTH; x++) {
                        int cb0 = (neigh_total0 >> x) & 1;
                        int cb1 = (neigh_total1 >> x) & 1;
                        int cb2 = (neigh_total2 >> x) & 1;
                        int cb3 = (neigh_total3 >> x) & 1;
                        int ub0 = (neigh_unk_total0 >> x) & 1;
                        int ub1 = (neigh_unk_total1 >> x) & 1;
                        int ub2 = (neigh_unk_total2 >> x) & 1;
                        int ub3 = (neigh_unk_total3 >> x) & 1;
                        int v = (mid >> x) & 1;
                        v += ((mid_unk >> x) & 1) << 1;
                        int nv = (is_live >> x) & 1;
                        nv += ((is_unk >> x) & 1) << 1;
                        printf("%d, %d: v=%d, count=%d, unk=%d, new=%d, abort %x\n",
                               x, y, v, (cb3 * 8) + (cb2 * 4) + (cb1 * 2) + cb0,
                               (ub3 * 8) + (ub2 * 4) + (ub1 * 2) + ub0, nv, abort);

                }
#endif

                // We have our result!

                out->bit0[y] = is_live;
                out->bit1[y] = is_unk;
                any_active |= (t->bit0[y] ^ is_live) | (t->bit1[y] ^ is_unk);

                // Shift the previous results
                up_total0 = mid_total0; up_total1 = mid_total1;
                mid_total0 = down_total0; mid_total1 = down_total1;
                up = mid; mid = down;

                up_unk_total0 = mid_unk_total0; up_unk_total1 = mid_unk_total1;
                mid_unk_total0 = down_unk_total0; mid_unk_total1 = down_unk_total1;
                up_unk = mid_unk; mid_unk = down_unk;
        }

        if(abort != 0)
                flags |= ABORT;

        if(any_active != 0)
                flags |= ACTIVE;

        return flags;
}
