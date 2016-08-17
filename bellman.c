#include <string.h>
#include <stdlib.h>
#include <getopt.h>
#include <time.h>
#include <assert.h>
#include <inttypes.h>
#include "universe.h"
#include "readwrite.h"
#include "bitwise.h"

// REINTRODUCTION OF FIXED CATALYSTS
// int ver_cats (generation *ge);

#define YES 1
#define NO 0

#define program_name "Bellman_szlim"
#define version_string "v0.74"

// Remember this unexpected condition but let the search continue:
static int got_to_end_of_pattern = NO;


static const char *PARM_OLD_FIRST_ENC =				"first-encounter";
static const char *PARM_OLD_LAST_ENC =				"last-encounter";
static const char *PARM_OLD_REPAIR_INT =			"repair-interval";
static const char *PARM_OLD_STABLE_INT =			"stable-interval";
static const char *PARM_OLD_MAX_LIVE =				"max-live";
static const char *PARM_OLD_MAX_ACT =				"max-active";

static const char *PARM_MIN_FIRST_ACT_GEN =			"min-first-active-gen";
static const char *PARM_MAX_FIRST_ACT_GEN =			"max-first-active-gen";
static const char *PARM_STRICTLY_GEN_BY_GEN =		"strictly-gen-by-gen";
static const char *PARM_MAX_LAST_ACT_GEN =			"max-last-active-gen";
static const char *PARM_MAX_ACT_WINDOW_GENS =		"max-active-window-gens";
static const char *PARM_MAX_CONS_ACT_GENS =			"max-active-gens-in-a-row";
static const char *PARM_ACCEPT1_INACT_GENS =		"accept-alt1-inactive-gens";
static const char *PARM_ACCEPT2_ACT_INACT_GENS =	"accept-alt2-active-inactive-gens";
static const char *PARM_ACCEPT2_MIN_INACT_GENS =	"accept-alt2-min-inactive-gens";
static const char *PARM_CONT_AFTER_ACCEPT =			"continue-after-accept";
static const char *PARM_MAX_ADDED_STATIC_ON =		"max-added-static-oncells";
static const char *PARM_MAX_ACT_CELLS =				"max-active-cells";
static const char *PARM_FILTER_MIN_ACT_CELLS =		"filter-below-min-active-cells";
static const char *PARM_MAX_LOCAL_RECT_COMPL =		"max-local-rect-complexity";
static const char *PARM_MAX_OVERALL_LOCAL_COMPL =	"max-overall-local-complexity";
static const char *PARM_MAX_LOCAL_RECTS =			"max-local-rects";
static const char *PARM_MIN_RECT_SEPARATION_SQ =	"min-rect-separation-squared";
static const char *PARM_MAX_GLOBAL_COMPL =			"max-global-complexity";
static const char *PARM_NEW_RESULT_NAMING =			"new-result-naming";

static const char *PARM_SYM_HORZ_ODD =				"symmetry-horiz-odd";
static const char *PARM_SYM_HORZ_EVEN =				"symmetry-horiz-even";
static const char *PARM_SYM_VERT_ODD =				"symmetry-vert-odd";
static const char *PARM_SYM_VERT_EVEN =				"symmetry-vert-even";
static const char *PARM_SYM_DIAG =					"symmetry-diag";
static const char *PARM_SYM_DIAG_INV =				"symmetry-diag-inverse";


static universe *u_static, *u_evolving, *u_forbidden, *u_filter;

// Limits to use in buffer allocations
#define MAX_MAX_ADDED_STATIC_ON 1024
#define MAX_MAX_LOCAL_RECTS 32
#define MAX_MAX_UNMERGED_LOCAL_RECTS (4 * MAX_MAX_LOCAL_RECTS)
#define MAX_LISTED_ACTIVATIONS 32

#define LOCAL_RECT_FREE_CELLS 4
#define LOCAL_COMPL_OVERALL_FREE_CELLS 9
#define GLOBAL_COMPL_FREE_CELLS 9

#define PARM_NOT_SET -2
#define PARM_DISABLED -1

// Default values for search parameters:
#define DEF_MIN_FIRST_ACT_GEN 2
#define DEF_FIRST_ACT_GEN_SPAN 16
#define DEF_ACT_GEN_SPAN 32
#define DEF_MAX_CONS_ACT_GENS 16
#define DEF_ACCEPT1_INACT_GENS 6
#define DEF_ACCEPT2_MIN_INACT_GENS 2
#define DEF_MAX_ACT_CELLS 8
#define DEF_MAX_LOCAL_RECTS 2
#define DEF_MIN_RECT_SEPARATION_SQ 8

// Search parameters:
// Note that if both max_last_act_gen and max_act_window_gens are expicitly set to a value,
// max_last_act_gen will be lowered to (max_first_act_gen + max_act_window_gens - 1) if applicable

static int filter_min_act_cells = PARM_NOT_SET;

static int min_first_act_gen = PARM_NOT_SET;
static int max_first_act_gen = PARM_NOT_SET;
static int strictly_gen_by_gen = PARM_NOT_SET;
static int max_last_act_gen = PARM_NOT_SET;
static int max_act_window_gens = PARM_NOT_SET;
static int max_cons_act_gens = PARM_NOT_SET;
static int accept1_inact_gens = PARM_NOT_SET;
static int accept2_act_inact_gens = PARM_NOT_SET;
static int accept2_min_inact_gens = PARM_NOT_SET;
static int cont_after_accept = PARM_NOT_SET;
static int max_added_static_on = PARM_NOT_SET;
static int max_act_cells = PARM_NOT_SET;
static int max_local_rect_compl = PARM_NOT_SET;
static int max_overall_local_compl = PARM_NOT_SET;
static int max_local_rects = PARM_NOT_SET;
static int min_rect_separation_sq = PARM_NOT_SET;
static int max_global_compl = PARM_NOT_SET;
static int new_result_naming = PARM_NOT_SET;

// Symmetry constraints
static enum {
	NONE, HORIZ, VERT, DIAG, DIAG_INVERSE
} symmetry_type = NONE;

static int symmetry_ofs = 0;

// static int diagonal_x, diagonal_y;
// static int inverse_x, inverse_y;


// Other global values
static int dumpcount = 0;
static int solcount = 0;
static int max_gens;
static int current_single_gen = -1;


// List of currently added static on-cells
static int onlist_x [MAX_MAX_ADDED_STATIC_ON];
static int onlist_y [MAX_MAX_ADDED_STATIC_ON];
static int onlist_cnt = 0;


// Status update values and prune counters
#define STATUS_UPDATE_INTERVAL 10.0

static time_t start_time;
static time_t last_print_time = 0;
static time_t last_sol_time = 0;
static time_t last_new_gen_time = 0;
static uint64_t last_total_prunes = 0;

static int uses_forbidden = NO;
static int uses_explicit_filter = NO;

static uint64_t prune_unstable = 0;
static uint64_t prune_stopped_adding_oncells = 0;
static uint64_t prune_forbidden = 0;
static uint64_t prune_solution = 0;
static uint64_t prune_no_cont_found = 0;
static uint64_t prune_explicit_filter_prune = 0;
static uint64_t prune_explicit_filter_filtered = 0;
static uint64_t prune_filter_too_few_act_cells = 0;

static uint64_t prune_first_acty_too_early = 0;
static uint64_t prune_no_acty_in_time = 0;
static uint64_t prune_acty_too_late = 0;
static uint64_t prune_acty_window_too_long = 0;
static uint64_t prune_cons_acty_too_long = 0;
static uint64_t prune_too_many_added_static_on = 0;
static uint64_t prune_too_many_act_cells = 0;
static uint64_t prune_too_compl_local_rect = 0;
static uint64_t prune_too_compl_overall_locally = 0;
static uint64_t prune_too_many_local_rects = 0;
static uint64_t prune_too_compl_globally = 0;


static int assert_if_debug (int a)
{
	(void) a;
	return YES;
}

static int lowest_of (int arg1, int arg2)
{
	if (arg2 < arg1)
		return arg2;
	else
		return arg1;
}

static int highest_of (int arg1, int arg2)
{
	if (arg2 > arg1)
		return arg2;
	else
		return arg1;
}


static void do_prune_line (const char *text, uint64_t count, uint64_t *total)
{
	printf ("    %s: %" PRIu64 "\n", text, count);
	*total += count;
}

static void print_elapsed (uint64_t elapsed)
{
	int days = (int) (elapsed / (24 * 60 * 60));
	int hours = (int) ((elapsed % (24 * 60 * 60)) / (60 * 60));
	int mins = (int) ((elapsed % (60 * 60)) / 60);
	int secs = (int) (elapsed % 60);
	
	if (days)
		printf ("(ddd:hh:mm:ss) %03d:%02d:%02d:%02d", days, hours, mins, secs);
	else
		printf ("%02d:%02d:%02d", hours, mins, secs);
}

static void print_prune_counters (int force)
{
	time_t time_now = time (NULL);
	
	if (last_print_time == 0)
		last_print_time = time_now;
	
	double time_since_last_print = difftime (time_now, last_print_time);
	
	if (time_since_last_print >= STATUS_UPDATE_INTERVAL || force)
	{
		uint64_t total_prunes = 0;
		
		printf("  Reasons why search space was pruned:\n");
		do_prune_line ("Static pattern is unstable", prune_unstable, &total_prunes);
		do_prune_line ("Stopped adding new on-cells", prune_stopped_adding_oncells, &total_prunes);
		if (uses_forbidden)
			do_prune_line ("Hit forbidden region", prune_forbidden, &total_prunes);
		if (!cont_after_accept)
			do_prune_line ("Found a solution", prune_solution, &total_prunes);
		else
			do_prune_line ("No continuation found", prune_no_cont_found, &total_prunes);
		if (uses_explicit_filter)
		{
			do_prune_line ("Filter mismatch, pruned before solution", prune_explicit_filter_prune, &total_prunes);
			do_prune_line ("Filter mismatch, solution filtered", prune_explicit_filter_filtered, &total_prunes);
		}
		if (filter_min_act_cells != PARM_DISABLED)
			do_prune_line ("Filtered, too few active cells", prune_filter_too_few_act_cells, &total_prunes);
		
		if (min_first_act_gen > 0)
			do_prune_line ("First activity too early", prune_first_acty_too_early, &total_prunes);
		do_prune_line ("Did not become active in time", prune_no_acty_in_time, &total_prunes);
		if (max_act_window_gens == PARM_DISABLED || max_last_act_gen < max_first_act_gen + max_act_window_gens - 1)
			do_prune_line ("Activity after last allowed active generation", prune_acty_too_late, &total_prunes);
		if (max_act_window_gens != PARM_DISABLED)
			do_prune_line ("Activity window lasted too long", prune_acty_window_too_long, &total_prunes);
		if (max_cons_act_gens != PARM_DISABLED)
			do_prune_line ("Too many active generations in a row", prune_cons_acty_too_long, &total_prunes);
		if (max_added_static_on != PARM_DISABLED)
			do_prune_line ("Too many added static on-cells", prune_too_many_added_static_on, &total_prunes);
		if (max_act_cells != PARM_DISABLED)
			do_prune_line ("Too many active cells", prune_too_many_act_cells, &total_prunes);
		if (max_local_rect_compl != PARM_DISABLED)
			do_prune_line ("Local rectangle too complex", prune_too_compl_local_rect, &total_prunes);
		if (max_overall_local_compl != PARM_DISABLED)
			do_prune_line ("Too high overall local complexity", prune_too_compl_overall_locally, &total_prunes);
		if (max_local_rects != PARM_DISABLED)
			do_prune_line ("Too many local rectangles", prune_too_many_local_rects, &total_prunes);
		if (max_global_compl != PARM_DISABLED)
			do_prune_line ("Too complex globally", prune_too_compl_globally, &total_prunes);
		
		if (uses_explicit_filter || filter_min_act_cells != PARM_DISABLED)
			printf("  Solutions: %d (and %" PRIu64 " filtered), prunes: %" PRIu64 "\n", solcount, prune_explicit_filter_filtered + prune_filter_too_few_act_cells, total_prunes);
		else
			printf("  Solutions: %d, prunes: %" PRIu64 "\n", solcount, total_prunes);
		
		double total_time = difftime (time_now, start_time);
		if (total_time > 0.0)
		{
			printf ("  Average: %.3f Kprunes/s", (double) total_prunes / total_time / 1000.0);
			if (time_since_last_print > 0.0)
				printf (", current: = %.3f Kprunes/s", ((double) (total_prunes - last_total_prunes) / time_since_last_print) / 1000.0);
			printf ("\n");
		}
		
		if (solcount > 0)
		{
			printf ("  Time since last solution: ");
			print_elapsed ((uint64_t) difftime (time_now, last_sol_time));
			printf ("\n");
		}
		
		if (strictly_gen_by_gen && max_first_act_gen > min_first_act_gen)
		{
			printf ("  Searching generation %d (%d of %d complete)\n", current_single_gen, current_single_gen - min_first_act_gen, max_first_act_gen - min_first_act_gen + 1);
			printf ("  Time since start of current generation: ");
			print_elapsed ((uint64_t) difftime (time_now, last_new_gen_time));
			printf ("\n");
		}
		
		printf ("Total time: ");
		print_elapsed ((uint64_t) total_time);
		printf ("\n");
		
		last_print_time = time_now;
		last_total_prunes = total_prunes;
	}
}


static void read_cb(void *u_, char area, int gen, int x, int y, char c) {
	cellvalue vs = OFF, ve = OFF, vf = OFF;
	
	(void)u_;
	
	if((area == 'P') && (gen == 0)) {
		switch(c) {
		case '.':
		case ' ':
			break;
		case '*': vs = ve = ON; break;
		case '@': ve = ON; break;
		case '?': vs = ve = UNKNOWN_STABLE; break;
		case '!': vs = ve = UNKNOWN_STABLE; vf = ON; uses_forbidden = YES; break;
		default:
			fprintf (stderr, "Unknown character '%c' in pattern definition\n", c);
			exit (-1);
		}
		
		generation_set_cell(u_static->first, x, y, vs);
		generation_set_cell(u_evolving->first, x, y, ve);
		generation_set_cell(u_forbidden->first, x, y, vf);
	} else if(area == 'F') {
		uses_explicit_filter = YES;
		generation *g = universe_find_generation(u_filter, gen, 1);
		
		switch(c)
		{
			case '*' :
			case '@' :
				generation_set_cell(g, x, y, ON);
				break;
			case '.' :
			case ' ' :
				generation_set_cell(g, x, y, OFF);
				break;
			case '?':
			case '!':
				fprintf (stderr, "Character '%c' is not supported in filter definition\n", c);
				exit (-1);
			default:
				fprintf (stderr, "Unknown character '%c' in filter definition\n", c);
				exit (-1);
		}
	}
}

static int match_parameter (const char *match, const char *param, const char *valuein, int minvalue, int maxvalue, int *valueout)
{
	if (strcmp (match, param) != 0)
		return NO;
	
	int value = strtol (valuein, NULL, 10);
	
	if (value != PARM_DISABLED && (value < minvalue || value > maxvalue))
	{
		fprintf (stderr, "Legal range for parameter '%s' is %d to %d, or set to %d to disable\n", match, minvalue, maxvalue, PARM_DISABLED);
		exit (-1);
	}
	
	*valueout = value;
	return YES;
}

static void read_param_cb(void *u_, const char *param, const char *value) {
	(void)u_;
	int match = NO;
	int coord;
	
	int old_repair_int = PARM_NOT_SET;
	int old_stable_int = PARM_NOT_SET;
	
	// Traditional paramterers for (some) backward compatibility
	match |= match_parameter (PARM_OLD_FIRST_ENC, param, value, 0, 2047, &min_first_act_gen);
	match |= match_parameter (PARM_OLD_LAST_ENC, param, value, 0, 2047, &max_first_act_gen);
	match |= match_parameter (PARM_OLD_REPAIR_INT, param, value, 1, 2047, &old_repair_int);
	match |= match_parameter (PARM_OLD_STABLE_INT, param, value, 1, 2047, &old_stable_int);
	match |= match_parameter (PARM_OLD_MAX_LIVE, param, value, 0, MAX_MAX_ADDED_STATIC_ON, &max_added_static_on);
	match |= match_parameter (PARM_OLD_MAX_ACT, param, value, 0, 2047, &max_act_cells);
	
	if (old_repair_int != PARM_NOT_SET)
	{
		if (old_repair_int == PARM_DISABLED)
			max_cons_act_gens = PARM_DISABLED;
		else
			max_cons_act_gens = old_repair_int + 1;
	}
	
	if (old_stable_int != PARM_NOT_SET)
	{
		if (old_stable_int == PARM_DISABLED)
			accept1_inact_gens = PARM_DISABLED;
		else
			accept1_inact_gens = old_stable_int + 1;
	}
	
	// New style parameters
	match |= match_parameter (PARM_MIN_FIRST_ACT_GEN, param, value, 0, 2047, &min_first_act_gen);
	match |= match_parameter (PARM_MAX_FIRST_ACT_GEN, param, value, 0, 2047, &max_first_act_gen);
	match |= match_parameter (PARM_STRICTLY_GEN_BY_GEN, param, value, 0, 1, &strictly_gen_by_gen);
	match |= match_parameter (PARM_MAX_LAST_ACT_GEN, param, value, 0, 2047, &max_last_act_gen);
	match |= match_parameter (PARM_MAX_ACT_WINDOW_GENS, param, value, 1, 2047, &max_act_window_gens);
	match |= match_parameter (PARM_MAX_CONS_ACT_GENS, param, value, 1, 2047, &max_cons_act_gens);
	match |= match_parameter (PARM_ACCEPT1_INACT_GENS, param, value, 1, 2047, &accept1_inact_gens);
	match |= match_parameter (PARM_ACCEPT2_ACT_INACT_GENS, param, value, 2, 2047, &accept2_act_inact_gens);
	match |= match_parameter (PARM_ACCEPT2_MIN_INACT_GENS, param, value, 1, 2047, &accept2_min_inact_gens);
	match |= match_parameter (PARM_CONT_AFTER_ACCEPT, param, value, 0, 1, &cont_after_accept);
	match |= match_parameter (PARM_MAX_ADDED_STATIC_ON, param, value, 0, MAX_MAX_ADDED_STATIC_ON, &max_added_static_on);
	match |= match_parameter (PARM_MAX_ACT_CELLS, param, value, 0, 2047, &max_act_cells);
	match |= match_parameter (PARM_FILTER_MIN_ACT_CELLS, param, value, 1, 2047, &filter_min_act_cells);
	match |= match_parameter (PARM_MAX_LOCAL_RECT_COMPL, param, value, 0, 2047, &max_local_rect_compl);
	match |= match_parameter (PARM_MAX_OVERALL_LOCAL_COMPL, param, value, 0, 2047, &max_overall_local_compl);
	match |= match_parameter (PARM_MAX_LOCAL_RECTS, param, value, 1, MAX_MAX_LOCAL_RECTS, &max_local_rects);
	match |= match_parameter (PARM_MIN_RECT_SEPARATION_SQ, param, value, 0, 524287, &min_rect_separation_sq);
	match |= match_parameter (PARM_MAX_GLOBAL_COMPL, param, value, 0, 2047, &max_global_compl);
	match |= match_parameter (PARM_NEW_RESULT_NAMING, param, value, 0, 1, &new_result_naming);
	
	if(!strcmp(param, PARM_SYM_HORZ_ODD)) {
		coord = strtol(value, NULL, 10);
		symmetry_type = HORIZ;
		symmetry_ofs = (coord * 2);
	}
	else if(!strcmp(param, PARM_SYM_HORZ_EVEN)) {
		coord = strtol(value, NULL, 10);
		symmetry_type = HORIZ;
		symmetry_ofs = (coord * 2) + 1;
	}
	else if(!strcmp(param, PARM_SYM_VERT_ODD)) {
		coord = strtol(value, NULL, 10);
		symmetry_type = VERT;
		symmetry_ofs = (coord * 2);
	}
				
	else if(!strcmp(param, PARM_SYM_VERT_EVEN)) {
		coord = strtol(value, NULL, 10);
		symmetry_type = VERT;
		symmetry_ofs = (coord * 2) + 1;
	}
	else if(!strcmp(param, PARM_SYM_DIAG)) {
		fprintf (stderr, "Symmetry type '%s' is not implemented\n", PARM_SYM_DIAG);
		exit (-1);
		
//		if(sscanf(value, "%d %d", &diagonal_x, &diagonal_y) != 2) {
//			fprintf(stderr, "Bad symmetry parameter: '%s'\n", value);
//			exit(-1);
//		}
//		
//		symmetry_type = DIAG;
	}
	
	else if(!strcmp(param, PARM_SYM_DIAG_INV)) {
		fprintf (stderr, "Symmetry type '%s' is not implemented\n", PARM_SYM_DIAG_INV);
		exit (-1);
		
//		if(sscanf(value, "%d %d", &inverse_x, &inverse_y) != 2) {
//			fprintf(stderr, "Bad symmetry parameter: '%s'\n", value);
//			exit(-1);
//		}
//		
//		symmetry_type = DIAG_INVERSE;
	}
	
	else if (!match)
	{
		fprintf(stderr, "Unknown parameter: '%s'\n", param);
		exit (-1);
	}
}

static int verify_and_fix_parameters ()
{
	if (min_first_act_gen == PARM_NOT_SET)
		min_first_act_gen = DEF_MIN_FIRST_ACT_GEN;
	else if (min_first_act_gen == PARM_DISABLED)
		min_first_act_gen = 0;
	
	if (max_first_act_gen == PARM_NOT_SET)
		max_first_act_gen = min_first_act_gen + DEF_FIRST_ACT_GEN_SPAN - 1;
	else if (max_first_act_gen == PARM_DISABLED)
		if (max_last_act_gen == PARM_NOT_SET)
			max_first_act_gen = min_first_act_gen + DEF_ACT_GEN_SPAN - 1;
		else if (max_last_act_gen == PARM_DISABLED)
		{
			fprintf (stderr, "If parameter '%s' is disabled, then parameter '%s' may not be disabled too\n", PARM_MAX_FIRST_ACT_GEN, PARM_MAX_LAST_ACT_GEN);
			return NO;
		}
		else
			max_first_act_gen = max_last_act_gen;
	else if (max_first_act_gen < min_first_act_gen)
	{
		fprintf (stderr, "Parameter '%s' may not be lower than parameter '%s'\n", PARM_MAX_FIRST_ACT_GEN, PARM_MIN_FIRST_ACT_GEN);
		return NO;
	}
	
	if (strictly_gen_by_gen == PARM_NOT_SET || strictly_gen_by_gen == PARM_DISABLED)
		strictly_gen_by_gen = 0;
	
	if (max_last_act_gen == PARM_NOT_SET)
		if (max_act_window_gens == PARM_NOT_SET || max_act_window_gens == PARM_DISABLED)
			max_last_act_gen = min_first_act_gen + DEF_ACT_GEN_SPAN - 1;
		else
			max_last_act_gen = max_first_act_gen + max_act_window_gens - 1;
	else if (max_last_act_gen == PARM_DISABLED)
		if (max_act_window_gens == PARM_NOT_SET || max_act_window_gens == PARM_DISABLED)
			max_last_act_gen = max_first_act_gen;
		else
			max_last_act_gen = max_first_act_gen + max_act_window_gens - 1;
	else if (max_last_act_gen < min_first_act_gen)
	{
		fprintf (stderr, "Parameter '%s' may not be lower than parameter '%s'\n", PARM_MAX_LAST_ACT_GEN, PARM_MIN_FIRST_ACT_GEN);
		return NO;
	}
	else if (max_act_window_gens != PARM_NOT_SET && max_act_window_gens != PARM_DISABLED && max_last_act_gen > max_first_act_gen + max_act_window_gens - 1)
		max_last_act_gen = max_first_act_gen + max_act_window_gens - 1;
	
	if (max_first_act_gen > max_last_act_gen)
	{
		max_first_act_gen = max_last_act_gen;
		fprintf (stderr, "Note: parameter '%s' is lower that parameter '%s'. Parameter '%s' takes precedence\n", PARM_MAX_LAST_ACT_GEN, PARM_MAX_FIRST_ACT_GEN, PARM_MAX_LAST_ACT_GEN);
	}
	
	if (max_act_window_gens == PARM_NOT_SET)
		max_act_window_gens = PARM_DISABLED;
	
	if (max_cons_act_gens == PARM_NOT_SET)
		max_cons_act_gens = DEF_MAX_CONS_ACT_GENS;
	
	if (accept1_inact_gens == PARM_NOT_SET)
		if (accept2_act_inact_gens == PARM_NOT_SET || accept2_act_inact_gens == PARM_DISABLED)
			accept1_inact_gens = DEF_ACCEPT1_INACT_GENS;
		else
			accept1_inact_gens = PARM_DISABLED;
	else if (accept1_inact_gens == PARM_DISABLED)
		if (accept2_act_inact_gens == PARM_NOT_SET || accept2_act_inact_gens == PARM_DISABLED)
		{
			fprintf (stderr, "Parameter '%s' may not be disabled unless parameter '%s' is set to an explicit value\n", PARM_ACCEPT1_INACT_GENS, PARM_ACCEPT2_ACT_INACT_GENS);
			return NO;
		}
	
	if (accept2_act_inact_gens == PARM_NOT_SET)
		accept2_act_inact_gens = PARM_DISABLED;
	
	if (accept2_min_inact_gens == PARM_NOT_SET)
	{
		accept2_min_inact_gens = DEF_ACCEPT2_MIN_INACT_GENS;
		if (accept2_act_inact_gens != PARM_DISABLED && accept2_min_inact_gens > accept2_act_inact_gens - 1)
			accept2_min_inact_gens = accept2_act_inact_gens - 1;
	}
	else if (accept2_min_inact_gens == PARM_DISABLED)
		accept2_min_inact_gens = 1;
	else if (accept2_act_inact_gens != PARM_DISABLED && accept2_min_inact_gens > accept2_act_inact_gens - 1)
	{
		fprintf (stderr, "Parameter '%s' must be lower than parameter '%s'\n", PARM_ACCEPT2_MIN_INACT_GENS, PARM_ACCEPT2_ACT_INACT_GENS);
		return NO;
	}
	
	if (cont_after_accept == PARM_NOT_SET || cont_after_accept == PARM_DISABLED)
		cont_after_accept = 0;
	
	if (max_added_static_on == PARM_NOT_SET)
		max_added_static_on = PARM_DISABLED;
	
	if (max_act_cells == PARM_NOT_SET)
		max_act_cells = DEF_MAX_ACT_CELLS;
	
	if (filter_min_act_cells == PARM_NOT_SET)
		filter_min_act_cells = PARM_DISABLED;
	else if (max_act_cells != PARM_DISABLED && filter_min_act_cells > max_act_cells)
	{
		fprintf (stderr, "Parameter '%s' may not be higher than parameter '%s'\n", PARM_FILTER_MIN_ACT_CELLS, PARM_MAX_ACT_CELLS);
		return NO;
	}
	
	if (max_local_rect_compl == PARM_NOT_SET)
		max_local_rect_compl = PARM_DISABLED;
	
	if (max_overall_local_compl == PARM_NOT_SET)
		max_overall_local_compl = PARM_DISABLED;
	
	if (max_local_rects == PARM_NOT_SET)
		max_local_rects = DEF_MAX_LOCAL_RECTS;
	else if (max_local_rects == PARM_DISABLED)
		if (max_local_rect_compl != PARM_DISABLED || max_overall_local_compl != PARM_DISABLED)
		{
			fprintf (stderr, "Parameter '%s' may not be disabled unless parameter '%s' and parameter '%s' are both disabled too\n", PARM_MAX_LOCAL_RECTS, PARM_MAX_LOCAL_RECT_COMPL, PARM_MAX_OVERALL_LOCAL_COMPL);
			return NO;
		}
	
	if (min_rect_separation_sq == PARM_NOT_SET)
		min_rect_separation_sq = DEF_MIN_RECT_SEPARATION_SQ;
	else if (min_rect_separation_sq == PARM_DISABLED)
		if (max_local_rect_compl != PARM_DISABLED || max_overall_local_compl != PARM_DISABLED)
		{
			fprintf (stderr, "Parameter '%s' may not be disabled unless parameter '%s' and parameter '%s' are both disabled too\n", PARM_MIN_RECT_SEPARATION_SQ, PARM_MAX_LOCAL_RECT_COMPL, PARM_MAX_OVERALL_LOCAL_COMPL);
			return NO;
		}
	
	if (max_global_compl == PARM_NOT_SET)
		max_global_compl = PARM_DISABLED;
	
	if (new_result_naming == PARM_NOT_SET || new_result_naming == PARM_DISABLED)
		new_result_naming = 0;
	
	return YES;
}	

static evolve_result bellman_evolve(tile *t, tile *out) {
	
	// Our evolution function is based on the 3 state Life variant.
	out->flags = tile_evolve_bitwise_3state(t, out) | CHANGED;
	
	// But we do another pass to (a) stop the UNKNOWN_STABLE area
	// from growing and (b) check for boundary condition
	// violations.
	
	tile *stable = (tile *)t->auxdata;
	if(!stable) return out->flags;
	tile *forbidden = (tile *)stable->auxdata;
	tile *filter = t->filter;
	tile *prev = t->prev;
	
	int y;
	
	TILE_WORD ul_bit0, u_bit0, ur_bit0;
	TILE_WORD ul_bit1, u_bit1, ur_bit1;
	TILE_WORD ul_bit0s, u_bit0s, ur_bit0s;
	TILE_WORD ul_bit1s, u_bit1s, ur_bit1s;
	
	tile *t_up = t->up;
	
	
	if(t_up) {
		GET3WORDS(ul_bit0, u_bit0, ur_bit0, t_up, 0, TILE_HEIGHT-1);
		GET3WORDS(ul_bit1, u_bit1, ur_bit1, t_up, 1, TILE_HEIGHT-1);
	} else {
		ul_bit0 = u_bit0 = ur_bit0 = 0;
		ul_bit1 = u_bit1 = ur_bit1 = 0;
	}
	
	t_up = stable->up;
	if(t_up) {
		GET3WORDS(ul_bit0s, u_bit0s, ur_bit0s, t_up, 0, TILE_HEIGHT-1);
		GET3WORDS(ul_bit1s, u_bit1s, ur_bit1s, t_up, 1, TILE_HEIGHT-1);
	} else {
		ul_bit0s = u_bit0s = ur_bit0s = 0;
		ul_bit1s = u_bit1s = ur_bit1s = 0;
	}
	
	
	TILE_WORD l_bit0, bit0, r_bit0;
	TILE_WORD l_bit1, bit1, r_bit1;
	TILE_WORD l_bit0s, bit0s, r_bit0s;
	TILE_WORD l_bit1s, bit1s, r_bit1s;
	
	GET3WORDS(l_bit0, bit0, r_bit0, t, 0, 0);
	GET3WORDS(l_bit1, bit1, r_bit1, t, 1, 0);
	GET3WORDS(l_bit0s, bit0s, r_bit0s, stable, 0, 0);
	GET3WORDS(l_bit1s, bit1s, r_bit1s, stable, 1, 0);
	
	TILE_WORD dl_bit0, d_bit0, dr_bit0;
	TILE_WORD dl_bit1, d_bit1, dr_bit1;
	TILE_WORD dl_bit0s, d_bit0s, dr_bit0s;
	TILE_WORD dl_bit1s, d_bit1s, dr_bit1s;
	TILE_WORD all_non_active = 0;
	
	TILE_WORD interaction = 0, activity = 0, unk_succ = 0, delta_from_stable_count = 0;
	TILE_WORD delta_from_previous_count = 0;
	TILE_WORD has_ON_cells = 0;
	
	TILE_WORD forbid = 0;
	TILE_WORD activity2 = 0, live = 0;
	TILE_WORD filter_diff_all = 0;
	
	for(y=0; y<TILE_HEIGHT; y++) {
		if(y == TILE_HEIGHT-1) {
			if(t->down) {
				GET3WORDS(dl_bit0, d_bit0, dr_bit0, t->down, 0, 0);
				GET3WORDS(dl_bit1, d_bit1, dr_bit1, t->down, 1, 0);
			} else {
				dl_bit0 = d_bit0 = dr_bit0 = 0;
				dl_bit1 = d_bit1 = dr_bit1 = 0;
			}
			if(stable->down) {
				GET3WORDS(dl_bit0s, d_bit0s, dr_bit0s, stable->down, 0, 0);
				GET3WORDS(dl_bit1s, d_bit1s, dr_bit1s, stable->down, 1, 0);
			} else {
				dl_bit0s = d_bit0s = dr_bit0s = 0;
				dl_bit1s = d_bit1s = dr_bit1s = 0;
			}
		} else {
			GET3WORDS(dl_bit0, d_bit0, dr_bit0, t, 0, y+1);
			GET3WORDS(dl_bit1, d_bit1, dr_bit1, t, 1, y+1);
			GET3WORDS(dl_bit0s, d_bit0s, dr_bit0s, stable, 0, y+1);
			GET3WORDS(dl_bit1s, d_bit1s, dr_bit1s, stable, 1, y+1);
		}
		
		// Note that this optimization is not implemented - all_non_active is always 0
		// If implemented, the filter checking may have to be moved outside of this if-clause
		if(all_non_active == 0)
		{
			// Any neighbourhood which is identical to the stable
			// universe should remain stable.
			
			TILE_WORD stable_diff_above = 0;
			stable_diff_above |= (ul_bit0s ^ ul_bit0);
			stable_diff_above |= (ul_bit1s ^ ul_bit1);
			stable_diff_above |= (u_bit0s ^ u_bit0);
			stable_diff_above |= (u_bit1s ^ u_bit1);
			stable_diff_above |= (ur_bit0s ^ ur_bit0);
			stable_diff_above |= (ur_bit1s ^ ur_bit1);
			
			TILE_WORD stable_diff_mid = 0;
			stable_diff_mid |= (l_bit0s ^ l_bit0);
			stable_diff_mid |= (l_bit1s ^ l_bit1);
			stable_diff_mid |= (bit0s ^ bit0);
			stable_diff_mid |= (bit1s ^ bit1);
			stable_diff_mid |= (r_bit0s ^ r_bit0);
			stable_diff_mid |= (r_bit1s ^ r_bit1);
			
			TILE_WORD stable_diff_below = 0;
			stable_diff_below |= (dl_bit0s ^ dl_bit0);
			stable_diff_below |= (dl_bit1s ^ dl_bit1);
			stable_diff_below |= (d_bit0s ^ d_bit0);
			stable_diff_below |= (d_bit1s ^ d_bit1);
			stable_diff_below |= (dr_bit0s ^ dr_bit0);
			stable_diff_below |= (dr_bit1s ^ dr_bit1);
			
			TILE_WORD diff_mask = stable_diff_above | stable_diff_mid | stable_diff_below;
			
			out->bit0[y] = (out->bit0[y] & diff_mask) | (stable->bit0[y] & ~diff_mask);
			out->bit1[y] = (out->bit1[y] & diff_mask) | (stable->bit1[y] & ~diff_mask);
			
			// Generate a mask representing anything that's set in
			// the stable region.
			TILE_WORD stable_set_above = 0;
			stable_set_above |= (ul_bit0s & ~ul_bit1s);
			stable_set_above |= (u_bit0s & ~u_bit1s);
			stable_set_above |= (ur_bit0s & ~ur_bit1s);
			
			TILE_WORD stable_set_mid = 0;
			stable_set_mid |= (l_bit0s & ~l_bit1s);
			stable_set_mid |= (bit0s & ~bit1s);
			stable_set_mid |= (r_bit0s & ~r_bit1s);
			
			TILE_WORD stable_set_below = 0;
			stable_set_below |= (dl_bit0s & ~dl_bit1s);
			stable_set_below |= (d_bit0s & ~d_bit1s);
			stable_set_below |= (dr_bit0s & ~dr_bit1s);
			
			TILE_WORD set_mask = stable_set_above | stable_set_mid | stable_set_below;
			
			// Look for places where the output differs from the
			// stable input
			TILE_WORD was0now1 = (~bit0s & ~bit1s) & (out->bit0[y] & ~out->bit1[y]);
			TILE_WORD was1now0 = (bit0s & ~bit1s) & (~out->bit0[y] & ~out->bit1[y]);
			
			TILE_WORD delta_from_stable = was0now1 | was1now0;
			
			live |= delta_from_stable;
			delta_from_stable &= set_mask;
			interaction |= delta_from_stable;
			
			// Have any forbidden cells changed?
			if(forbidden)
				forbid |= forbidden->bit0[y] & (was0now1 | was1now0);
			
			// Also count the number of cells which differ from
			// the stable input. 4 rounds of the bitwise bit
			// counting algorithm gets us to 16 bit subtotals
			// which we accumulate; we finish off the addition
			// outside the loop.
			
			// With a careful choice of tile size it should be
			// possible to move the last round out of the loop
			// too.
			
			delta_from_stable = (delta_from_stable & 0x5555555555555555) + ((delta_from_stable >> 1) & 0x5555555555555555);
			delta_from_stable = (delta_from_stable & 0x3333333333333333) + ((delta_from_stable >> 2) & 0x3333333333333333);
			delta_from_stable = (delta_from_stable & 0x0f0f0f0f0f0f0f0f) + ((delta_from_stable >> 4) & 0x0f0f0f0f0f0f0f0f);
			delta_from_stable = (delta_from_stable & 0x00ff00ff00ff00ff) + ((delta_from_stable >> 8) & 0x00ff00ff00ff00ff);
			
			delta_from_stable_count += delta_from_stable;
			
			// Look for places where the universe is changing
			was0now1 = (~bit0 & ~bit1) & (out->bit0[y] & ~out->bit1[y]);
			was1now0 = (bit0 & ~bit1) & (~out->bit0[y] & ~out->bit1[y]);
			TILE_WORD delta_from_previous = (was0now1 | was1now0);
			
			activity |= delta_from_previous;
			
			delta_from_previous &= set_mask;
			
			delta_from_previous = (delta_from_previous & 0x5555555555555555) + ((delta_from_previous >> 1) & 0x5555555555555555);
			delta_from_previous = (delta_from_previous & 0x3333333333333333) + ((delta_from_previous >> 2) & 0x3333333333333333);
			delta_from_previous = (delta_from_previous & 0x0f0f0f0f0f0f0f0f) + ((delta_from_previous >> 4) & 0x0f0f0f0f0f0f0f0f);
			delta_from_previous = (delta_from_previous & 0x00ff00ff00ff00ff) + ((delta_from_previous >> 8) & 0x00ff00ff00ff00ff);
			
			delta_from_previous_count += delta_from_previous;
			
			if(prev) {
				was0now1 = (~prev->bit0[y] & ~prev->bit1[y]) & (out->bit0[y] & ~out->bit1[y]);
				was1now0 = (prev->bit0[y] & ~prev->bit1[y]) & (~out->bit0[y] & ~out->bit1[y]);
				TILE_WORD delta_from_2prev = (was0now1 | was1now0);
				
				activity2 |= delta_from_2prev;
				
			}
			
			// Look for unknown successors
			unk_succ |= (out->bit1[y] & ~out->bit0[y]);
			
			//Update has on cells flag.
			has_ON_cells |= (~out->bit1[y] & out->bit0[y]);
			
			// Compare against user-specified filter pattern
			TILE_WORD filter_bit0 = filter ? filter->bit0[y] : 0;
			TILE_WORD filter_bit1 = filter ? filter->bit1[y] : (TILE_WORD)~0;
			
			TILE_WORD filter_diff = out->bit0[y] ^ filter_bit0;
			
			// Assume that unknown cells will not match the filter, to avoid getting false solutions
			// To avoid pruning valid solutions, the filter should only be tested when there are no evolving unknown cells, but only static unknown
			filter_diff &= ~filter_bit1;
			filter_diff_all |= filter_diff;
		}
		else
		{
			//if all activity is stable - remain the same (optimization, not implemented)
			out->bit0[y] = t->bit0[y];
			out->bit1[y] = t->bit1[y];
		}

		// Shift the previous results
		ul_bit0 = l_bit0; u_bit0 = bit0; ur_bit0 = r_bit0;
		ul_bit1 = l_bit1; u_bit1 = bit1; ur_bit1 = r_bit1;
		
		l_bit0 = dl_bit0; bit0 = d_bit0; r_bit0 = dr_bit0;
		l_bit1 = dl_bit1; bit1 = d_bit1; r_bit1 = dr_bit1;
		
		ul_bit0s = l_bit0s; u_bit0s = bit0s; ur_bit0s = r_bit0s;
		ul_bit1s = l_bit1s; u_bit1s = bit1s; ur_bit1s = r_bit1s;
		
		l_bit0s = dl_bit0s; bit0s = d_bit0s; r_bit0s = dr_bit0s;
		l_bit1s = dl_bit1s; bit1s = d_bit1s; r_bit1s = dr_bit1s;
		
	}
	
	// The delta_from_stable and delta_from_previous counters are
	// still split into 16 bit subtotals; finish them off here
	
	delta_from_stable_count = (delta_from_stable_count & 0x0000ffff0000ffff) + ((delta_from_stable_count >> 16) & 0x0000ffff0000ffff);
	delta_from_stable_count = (delta_from_stable_count & 0x00000000ffffffff) + ((delta_from_stable_count >> 32) & 0x00000000ffffffff);
	
	delta_from_previous_count = (delta_from_previous_count & 0x0000ffff0000ffff) + ((delta_from_previous_count >> 16) & 0x0000ffff0000ffff);
	delta_from_previous_count = (delta_from_previous_count & 0x00000000ffffffff) + ((delta_from_previous_count >> 32) & 0x00000000ffffffff);
	
	out->n_active = delta_from_stable_count;
	out->delta_prev = delta_from_previous_count;
	
	if(interaction != 0) out->flags |= DIFFERS_FROM_STABLE;
	if(unk_succ != 0) out->flags |= HAS_UNKNOWN_CELLS;
	if(has_ON_cells != 0) out->flags |= HAS_ON_CELLS;
	if(forbid != 0) out->flags |= IN_FORBIDDEN_REGION;
	if(activity != 0) out->flags |= DIFFERS_FROM_PREVIOUS;
	if((activity2 != 0) || !prev) out->flags |= DIFFERS_FROM_2PREV;
	if(live != 0) out->flags |= IS_LIVE;
	if(filter_diff_all != 0) out->flags |= FILTER_MISMATCH;
	
	return out->flags;
}

static generation *bellman_evolve_generations(generation *g, int end) {
	tile *t;
	g->flags |= CHANGED;
	
	for(t = g->all_first; t; t = t->all_next)
		t->flags |= CHANGED;
	
	while((int) g->gen < end) {
		generation_evolve(g, bellman_evolve);
		g = g->next;
	}
	return g->prev;
}

static void dump(int full) {
	
	int i;
	
	printf("Dumping %d\n", dumpcount);
	
	if(full) {
		for(i=0; i<max_gens; i++) {
			printf("   %03d: %s\n", i,
				   flag2str(universe_find_generation(u_evolving, i, 0)->flags));
		}
	}
	dumpcount++;
}


static int is_on_cell (const generation *g, int x, int y)
{
	const tile *t = generation_find_tile ((generation *) g, x, y, NO);
	if (!t)
		return NO;
	
	return tile_get_cell ((tile *) t, x, y) & 0x01;
}

static int glider_bits [] = {0x008f, 0x015a, 0x006b, 0x011e, 0x012e, 0x0073, 0x00a7, 0x0172, 0x01e2, 0x00b5, 0x01ac, 0x00f1, 0x00e9, 0x019c, 0x01ca, 0x009d};

static int is_center_cell_of_glider (const generation *g, int x, int y)
{
	int bits = 0;
	int xi;
	int yi;
	
	for (xi = x - 1; xi <= x + 1; xi++)
		for (yi = y - 1; yi <= y + 1; yi++)
			bits = (bits << 1) | is_on_cell (g, xi, yi);
	
	int gl_ix;
	for (gl_ix = 0; gl_ix < 16; gl_ix++)
		if (bits == glider_bits [gl_ix])
		{
			int bix;
			for (bix = -2; bix < 2; bix++)
				if (is_on_cell (g, x + bix, y - 2) || is_on_cell (g, x + bix + 1, y + 2) || is_on_cell (g, x - 2, y + bix + 1) || is_on_cell (g, x + 2, y + bix))
					return NO;
			
			return YES;
		}
	
	return NO;
}

static int count_gliders (const generation *g)
{
	// Not very efficient, but only used for accepted solutions
	int gl_cnt = 0;
	
	const tile *t;
	for (t = g->all_first; t; t = t->all_next)
	{
		int xon;
		int xoff;
		int yon;
		int yoff;
		
		tile_find_bounds ((tile *) t, &xon, &xoff, &yon, &yoff);
		if (xon <= xoff)
		{
			// A tile that contains the center cell of a glider will have an on-cell in that tile, at most one cell diagonally
			// from it, but we need to limit the bounds to that of the tile, to not find a glider more than once
			
			// Change limits to first coordinate outside of bounds
			xoff += 1;
			yoff += 1;
			
			xon = highest_of (0, xon - 1) + t->xpos;
			xoff = lowest_of (TILE_WIDTH, xoff + 1) + t->xpos;
			yon = highest_of (0, yon - 1) + t->ypos;
			yoff = lowest_of (TILE_HEIGHT, yoff + 1) + t->ypos;
			
			int x;
			int y;
			
			for (x = xon; x < xoff; x++)
				for (y = yon; y < yoff; y++)
					if (is_center_cell_of_glider (g, x, y))
						gl_cnt++;
		}
	}
	
	return gl_cnt;
}

static void print_activation_gens (FILE *f, int act_count, int act_gen [])
{
	int a_ix;
	for (a_ix = 0; a_ix < act_count; a_ix++)
	{
		fprintf (f, "%d", act_gen [a_ix]);
		if (a_ix < act_count - 1)
			fprintf (f, ", ");
		else
			fprintf (f, "\n");
	}
}

static void bellman_found_solution (int accept_gen, int max_active, int glider_count, int act_count, int act_gen [])
{
	solcount++;
	last_sol_time = time (NULL);
	
	printf ("--- Found solution %d, accepted at gen %d, max active cells: %d\n", solcount, accept_gen, max_active);
	printf ("      Gliders: %d, activations at gen ", glider_count);
	print_activation_gens (stdout, act_count, act_gen);
	
	char name[30];
	tile *t;
	
	if (new_result_naming)
		snprintf(name, sizeof name, "result%06d.out", solcount);
	else
		snprintf(name, sizeof name, "result%06d-4.out", solcount);
	
	FILE *f = fopen(name, "w");
	if(f) {
		
		fprintf (f, "#S %s %d\n", PARM_MIN_FIRST_ACT_GEN, min_first_act_gen);
		fprintf (f, "#S %s %d\n", PARM_MAX_FIRST_ACT_GEN, max_first_act_gen);
		fprintf (f, "#S %s %d\n", PARM_STRICTLY_GEN_BY_GEN, strictly_gen_by_gen);
		fprintf (f, "#S %s %d\n", PARM_MAX_LAST_ACT_GEN, max_last_act_gen);
		fprintf (f, "#S %s %d\n", PARM_MAX_ACT_WINDOW_GENS, max_act_window_gens);
		fprintf (f, "#S %s %d\n", PARM_MAX_CONS_ACT_GENS, max_cons_act_gens);
		fprintf (f, "#S %s %d\n", PARM_ACCEPT1_INACT_GENS, accept1_inact_gens);
		fprintf (f, "#S %s %d\n", PARM_ACCEPT2_ACT_INACT_GENS, accept2_act_inact_gens);
		fprintf (f, "#S %s %d\n", PARM_ACCEPT2_MIN_INACT_GENS, accept2_min_inact_gens);
		fprintf (f, "#S %s %d\n", PARM_CONT_AFTER_ACCEPT, cont_after_accept);
		fprintf (f, "#S %s %d\n", PARM_MAX_ADDED_STATIC_ON, max_added_static_on);
		fprintf (f, "#S %s %d\n", PARM_MAX_ACT_CELLS, max_act_cells);
		fprintf (f, "#S %s %d\n", PARM_FILTER_MIN_ACT_CELLS, filter_min_act_cells);
		fprintf (f, "#S %s %d\n", PARM_MAX_LOCAL_RECT_COMPL, max_local_rect_compl);
		fprintf (f, "#S %s %d\n", PARM_MAX_OVERALL_LOCAL_COMPL, max_overall_local_compl);
		fprintf (f, "#S %s %d\n", PARM_MAX_LOCAL_RECTS, max_local_rects);
		fprintf (f, "#S %s %d\n", PARM_MIN_RECT_SEPARATION_SQ, min_rect_separation_sq);
		fprintf (f, "#S %s %d\n", PARM_MAX_GLOBAL_COMPL, max_global_compl);
		fprintf (f, "#S %s %d\n", PARM_NEW_RESULT_NAMING, new_result_naming);

		if (symmetry_type == HORIZ)
			if (symmetry_ofs & 0x00000001)
				fprintf (f, "#S %s %d\n", PARM_SYM_HORZ_ODD, symmetry_ofs / 2);
			else
				fprintf (f, "#S %s %d\n", PARM_SYM_HORZ_EVEN, (symmetry_ofs - 1) / 2);
		else if (symmetry_type == VERT)
		{
			if (symmetry_ofs & 0x00000001)
				fprintf (f, "#S %s %d\n", PARM_SYM_VERT_ODD, symmetry_ofs / 2);
			else
				fprintf (f, "#S %s %d\n", PARM_SYM_VERT_EVEN, (symmetry_ofs - 1) / 2);
		}
		
		fprintf (f, "#C Search made using %s, %s\n", program_name, version_string);
		fprintf (f, "#C Solution accepted at generation %d\n", accept_gen);
		fprintf (f, "#C Activations at generation ");
		print_activation_gens (f, act_count, act_gen);
		fprintf (f, "#C Max active cells %d\n", max_active);
		fprintf (f, "#C Glider count at accept %d\n", glider_count);
		
		for(t = u_static->first->all_first; t; t = t->all_next) {
			tile *t2 = universe_find_tile(u_evolving, 0, t->xpos, t->ypos, 0);
			fprintf(f, "#P %d %d\n", t->xpos, t->ypos);
			
			int x, y;
			
			for(y=0; y<TILE_HEIGHT; y++) {
				for(x=0; x<TILE_WIDTH; x++) {
					char c = '.';
					
					if(t2 && tile_get_cell(t2, x, y) == ON)
						c = '@';
					
					if(tile_get_cell(t, x, y) == ON)
						c = '*';
					else if(tile_get_cell(t, x, y) != OFF)
						c = '?';
					
					fputc(c, f);
				}
				fputc('\n', f);
			}
		}
		
		fclose(f);
	} else perror(name);
}

/*
typedef enum {FILTER_MATCH_NO, FILTER_MATCH_YES, FILTER_MATCH_UNKNOWN} filter_match;

static filter_match compare_filter_tile (const tile *filter, const tile *pattern)
{
	TILE_WORD mismatch = 0;
	TILE_WORD unknown = 0;

	int y;
	
	if (pattern)
		for (y = 0; y < TILE_HEIGHT; y++)
		{
			mismatch |= (filter->bit0 [y] ^ pattern->bit0 [y]) & ~(filter->bit1 [y] | pattern->bit1 [y]);
			unknown |= ~filter->bit1 [y] & pattern->bit1 [y];
		}
	else
		for (y = 0; y < TILE_HEIGHT; y++)
			mismatch |= filter->bit0 [y];
	
	if (mismatch)
		return FILTER_MATCH_NO;
	else if (unknown)
		return FILTER_MATCH_UNKNOWN;
	else
		return FILTER_MATCH_YES;
}

static filter_match test_filter (
{
}
*/

static int verify_static_is_stable ()
{
	// TODO: check only the neighbourhood of the cell we just modified!
	
	tile *t;
	for(t = u_static->first->all_first; t; t = t->all_next)
	{
		evolve_result res = tile_stabilise_3state (t, t->next);
		if (res & ABORT)
			return NO;
	}
	
	return YES;
}

// Forward declaration to allow mutual calls between bellman_choose_cells and bellman_recurse
static void bellman_choose_cells (universe *u, generation *g, int allow_new_oncells, int first_gen_with_unknown_cells, int first_next_sol_gen);

typedef enum {PHASE_NOT_ACTIVATED_YET, PHASE_ACTIVE, PHASE_RESTORED_NOT_YIELDED, PHASE_RESTORED_YIELDED} evolution_phase;

static int activation_gen [MAX_LISTED_ACTIVATIONS];

static void bellman_recurse (universe *u, generation *g, int allow_new_oncells, int previous_first_gen_with_unknown_cells, int first_next_sol_gen)
{
	print_prune_counters (NO);
		
	// First make sure the static pattern is truly static
	// Note that both a new static on-cell and a new static off-cell can cause the static pattern to become impossible to make stable
	if (!verify_static_is_stable ())
	{
		prune_unstable++;
		return;
	}
	
// REINTRODUCTION OF FIXED CATALYSTS
//	if (!ver_cats (g))
//		return;
	
	// Evolve any changes up to previous first gen with unknown cells
	generation *ge;
	for(ge = u->first; ge && ge->next; ge = ge->next)
	{
		if(ge->flags & CHANGED)
		{
			ge->flags &= ~CHANGED;
			generation_evolve(ge, bellman_evolve);
		}
		
		if ((int) ge->gen == previous_first_gen_with_unknown_cells)
			break;
	}
	
	// If there are still unknown cells in the same generation as before, just skip and pick another static cell to define
	if (!(ge->flags & HAS_UNKNOWN_CELLS))
	{
		// Now check that the evolving universe is behaving itself
		
		evolution_phase phase = PHASE_NOT_ACTIVATED_YET;
		int current_actn_first_gen = -1;
		int last_allowed_act_gen = max_last_act_gen;
		int last_allowed_act_limited_by_window = NO;
		int current_restoration_gen = -1;
		int unfiltered_accept_gen = -1;
		int max_n_active = 0;
		int n_activations = 0;
		
		for(ge = u->first; ge && ge->next; ge = ge->next)
		{
			if (ge->flags & CHANGED)
			{
				ge->flags &= ~CHANGED;
				generation_evolve(ge, bellman_evolve);
			}
			
			// When we see the next generation with unknown cells, we skip and pick more static cells to define.
			// Bellman used to go on with checking the generation here anyway. Which method is faster varies a lot with different search parameters.
			// Ideally Bellman should pick the most efficient method itself, but in a first step this choice of behavious could be made a search
			// parameter instead
			if (ge->flags & HAS_UNKNOWN_CELLS)
				break;
			
			int gen = (int) ge->gen;
			
			// Check if first activation should have happened by now
			if (phase == PHASE_NOT_ACTIVATED_YET && (gen > max_first_act_gen || (strictly_gen_by_gen && gen > current_single_gen)))
			{
				prune_no_acty_in_time++;
				return;
			}
			
			// Check for first activation
			// Verify that it doesn't happen too early
			if (phase == PHASE_NOT_ACTIVATED_YET && ge->n_active > 0)
			{
				if (gen < min_first_act_gen || (strictly_gen_by_gen && gen < current_single_gen))
				{
					prune_first_acty_too_early++;
					return;
				}
				else
				{
					phase = PHASE_ACTIVE;
					current_actn_first_gen = gen;
					if (max_act_window_gens != PARM_DISABLED && last_allowed_act_gen > gen + max_act_window_gens - 1)
					{
						last_allowed_act_gen = gen + max_act_window_gens - 1;
						last_allowed_act_limited_by_window = YES;
					}
					if (n_activations < MAX_LISTED_ACTIVATIONS)
						activation_gen [n_activations++] = gen;
				}
			}
			
			// We wanted to test for too early or too late activation first to spot any difference between normal mode and strictly-gen-by-gen mode
			// After that, test for too much activity first, for performance
			if (max_act_cells != PARM_DISABLED && (int) ge->n_active > max_act_cells)
			{
				prune_too_many_act_cells++;
				return;
			}
			
			max_n_active = highest_of (max_n_active, ge->n_active);
			
			// Check if all catalysts are restored and inactive after an ongoing activation
			if (phase == PHASE_ACTIVE && ge->n_active == 0)
			{
				phase = PHASE_RESTORED_NOT_YIELDED;
				current_restoration_gen = gen;
				
				if (accept1_inact_gens == PARM_DISABLED)
					unfiltered_accept_gen = highest_of (current_restoration_gen + accept2_min_inact_gens - 1, current_actn_first_gen + accept2_act_inact_gens - 1);
				else if (accept2_act_inact_gens == PARM_DISABLED)
				 	unfiltered_accept_gen = current_restoration_gen + accept1_inact_gens - 1;
				else
					unfiltered_accept_gen = lowest_of (current_restoration_gen + accept1_inact_gens - 1, highest_of (current_restoration_gen + accept2_min_inact_gens - 1, current_actn_first_gen + accept2_act_inact_gens - 1));
				
				if (accept2_act_inact_gens != PARM_DISABLED)
					unfiltered_accept_gen = lowest_of (unfiltered_accept_gen, highest_of (current_restoration_gen + accept2_min_inact_gens - 1, current_actn_first_gen + accept2_act_inact_gens - 1));
			}
			
			// Check for reactivation. This could be before the previous activation was accepted as a solution,
			// or it could be a search for further solutions if cont_after_accept is set. 
			if ((phase == PHASE_RESTORED_NOT_YIELDED || phase == PHASE_RESTORED_YIELDED) && ge->n_active > 0)
			{
				phase = PHASE_ACTIVE;
				current_actn_first_gen = gen;
				if (n_activations < MAX_LISTED_ACTIVATIONS)
					activation_gen [n_activations++] = gen;
			}
			
			// Check for activity after all activity should have stopped
			if (ge->n_active > 0 && gen > last_allowed_act_gen)
			{
				if (last_allowed_act_limited_by_window)
					prune_acty_window_too_long++;
				else
					prune_acty_too_late++;
				
				return;
			}
			
			// Note that if support is re-added for evaluating patterns with unknown evolving cells, this needs to be qualified with having no such cells
			if (ge->flags & FILTER_MISMATCH)
			{
				// Consider it a prune or a filtering depending on if the filter is applied before or after the solution should have been accepted without the filter
				if (phase == PHASE_RESTORED_NOT_YIELDED && gen >= unfiltered_accept_gen)
					prune_explicit_filter_filtered++;
				else
					prune_explicit_filter_prune++;
				return;
			}
			
			if (ge->flags & IN_FORBIDDEN_REGION)
			{
				prune_forbidden++;
				return;
			}
			
			// Check if an ongoing activation has lasted too long without break
			if (max_cons_act_gens != PARM_DISABLED && phase == PHASE_ACTIVE && gen > current_actn_first_gen + max_cons_act_gens + 1)
			{
				prune_cons_acty_too_long++;
				return;
			}
			
			// Check if all conditions for a solution are met
			if (phase == PHASE_RESTORED_NOT_YIELDED)
			{
				int accept_gen = highest_of (unfiltered_accept_gen, u_filter->n_gens - 1);
				
				if (gen >= accept_gen)
					phase = PHASE_RESTORED_YIELDED;
				
				if (gen == accept_gen && gen >= first_next_sol_gen)
				{
					// Filter out solutions that are too simple
					if (filter_min_act_cells == PARM_DISABLED || max_n_active >= filter_min_act_cells)
					{
						bellman_found_solution (gen, max_n_active, count_gliders (ge), n_activations, activation_gen);
						prune_solution++;
					}
					else
						prune_filter_too_few_act_cells++;
					
					if (cont_after_accept)
						first_next_sol_gen = gen + 1;
					else
						return;
				}
			}
			
			// Check if we can stop looking for a solution in continue_after_accept mode
			if (gen > last_allowed_act_gen && phase == PHASE_RESTORED_YIELDED)
			{
				prune_no_cont_found++;
				return;
			}
			
			// Stop adding new on-cells when it's too late to start a new activation and there is currently no ongoing activation
			// This prevents a lot of irrelevant solutions with extra pixels that don't activate
			if (gen > last_allowed_act_gen && (phase == PHASE_RESTORED_NOT_YIELDED || phase == PHASE_RESTORED_YIELDED))
				allow_new_oncells = NO;
		}
	}
	
	bellman_choose_cells(u, g, allow_new_oncells, ge->gen, first_next_sol_gen);
}

#define TRY(cdx, cdy)																										\
	if(tile_get_cell(t->prev, x + cdx, y + cdy) == UNKNOWN_STABLE && validate_xy_for_symmetry(x + cdx, y + cdy) == YES) {	\
		dx = cdx;																											\
		dy = cdy;																											\
		goto found;																											\
	}

static int validate_xy_for_symmetry(int x, int y)
{
	switch(symmetry_type) {
	case NONE:
		return YES;
	case HORIZ:
		if(y >= symmetry_ofs - y)
			return YES;
		else
			return NO;

	case VERT:
		if(x >= symmetry_ofs - x)
			return YES;
		else
			return NO;

	default:
		return NO;
	}
}

static int xy_symmetry(int x, int y, int* mirrorx_arr, int* mirrory_arr)
{
	mirrorx_arr[0] = x;
	mirrory_arr[0] = y;
	
	switch(symmetry_type) {
		case NONE:
			return 1;
		case HORIZ:
			if(y == symmetry_ofs - y)
				return 1;
			
			mirrorx_arr[1] = x;
			mirrory_arr[1] = symmetry_ofs - y;
			
			return 2;
			
		case VERT:
			if(x == symmetry_ofs - x)
				return 1;
			
			mirrorx_arr[1] =  symmetry_ofs - x;
			mirrory_arr[1] = y;
			
			return 2;
			
		default:
			return 1;
	}
}


static int distance_sq (int x1, int y1, int x2, int y2)
{
	return (x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1);
}

typedef enum {COMPL_OK, COMPL_FAILED_LOCAL_RECT, COMPL_FAILED_OVERALL_LOCALLY, COMPL_FAILED_TOO_MANY_RECTS, COMPL_FAILED_GLOBALLY} compl_result;

typedef struct
{
	int xon;
	int xoff;
	int yon;
	int yoff;
	int oncnt;
	int free_cells;
	int compl_limit;
} compl_box;

static void compl_box_init (compl_box *cb, int free_cells, int compl_limit)
{
	cb->xon = 0;
	cb->xoff = 0;
	cb->yon = 0;
	cb->yoff = 0;
	cb->oncnt = 0;
	cb->free_cells = free_cells;
	cb->compl_limit = compl_limit;
}

static void compl_box_copy (const compl_box *src, compl_box *dst)
{
	dst->xon = src->xon;
	dst->xoff = src->xoff;
	dst->yon = src->yon;
	dst->yoff = src->yoff;
	dst->oncnt = src->oncnt;
	dst->free_cells = src->free_cells;
	dst->compl_limit = src->compl_limit;
}

static void compl_box_add_cell (compl_box *cb, int x, int y)
{
	if (cb->oncnt == 0)
	{
		cb->xon = x;
		cb->xoff = x + 1;
		cb->yon = y;
		cb->yoff = y + 1;
	}
	else
	{
		cb->xon = lowest_of (cb->xon, x);
		cb->xoff = highest_of (cb->xoff, x + 1);
		cb->yon = lowest_of (cb->yon, y);
		cb->yoff = highest_of (cb->yoff, y + 1);
	}
	
	cb->oncnt++;
}

static void compl_box_merge (const compl_box *src, compl_box *dst)
{
	dst->xon = lowest_of (dst->xon, src->xon);
	dst->xoff = highest_of (dst->xoff, src->xoff);
	dst->yon = lowest_of (dst->yon, src->yon);
	dst->yoff = highest_of (dst->yoff, src->yoff);
	dst->oncnt += src->oncnt;
}

static int compl_box_size_compl (const compl_box *cb)
{
	int longside = highest_of (cb->xoff - cb->xon, cb->yoff - cb->yon);
	int shortside = lowest_of (cb->xoff - cb->xon, cb->yoff - cb->yon);
	
	return 2 * longside + shortside;
}

static int compl_box_within_limit (const compl_box *cb)
{
	return (compl_box_size_compl (cb) + highest_of (0, cb->oncnt - cb->free_cells)) <= cb->compl_limit;
}


static int box_cnt;
static compl_box temp_box [MAX_MAX_UNMERGED_LOCAL_RECTS];
static int box_of_cell [MAX_MAX_ADDED_STATIC_ON];

static void delete_compl_box (int del_ix, int new_cell_box)
{
	int cell_ix;
	for (cell_ix = 0; cell_ix < onlist_cnt; cell_ix++)
	{
		if (box_of_cell [cell_ix] == del_ix)
			box_of_cell [cell_ix] = new_cell_box;
		if (box_of_cell [cell_ix] > del_ix)
			box_of_cell [cell_ix]--;
	}
	
	int box_ix;
	for (box_ix = del_ix; box_ix < box_cnt - 1; box_ix++)
		compl_box_copy (&temp_box [box_ix + 1], &temp_box [box_ix]);
	
	box_cnt--;
}

static compl_result test_compl_locally ()
{
	int max_compl = (max_local_rect_compl == PARM_DISABLED) ? max_overall_local_compl : max_local_rect_compl;
	int free_cells = (max_local_rect_compl == PARM_DISABLED) ? LOCAL_COMPL_OVERALL_FREE_CELLS : LOCAL_RECT_FREE_CELLS;
	int fail_code = (max_local_rect_compl == PARM_DISABLED) ? COMPL_FAILED_OVERALL_LOCALLY : COMPL_FAILED_LOCAL_RECT;
	
	box_cnt = 0;
	
	int obj_ix;
	for (obj_ix = 0; obj_ix < onlist_cnt; obj_ix++)
	{
		box_of_cell [obj_ix] = -1;
		
		int ref_ix;
		for (ref_ix = 0; ref_ix < obj_ix; ref_ix++)
		{
			int dist_sq = distance_sq (onlist_x [obj_ix], onlist_y [obj_ix], onlist_x [ref_ix], onlist_y [ref_ix]);
			
			if (dist_sq < min_rect_separation_sq)
			{
				if (box_of_cell [obj_ix] == -1)
				{
					// obj_ix cell was not yet in a box, but it is close to a cell in an existing box, so add it to that box
					compl_box_add_cell (&temp_box [box_of_cell [ref_ix]], onlist_x [obj_ix], onlist_y [obj_ix]);
					if (!compl_box_within_limit (&temp_box [box_of_cell [ref_ix]]))
						return fail_code;
					
					box_of_cell [obj_ix] = box_of_cell [ref_ix];
				}
				else if (box_of_cell [obj_ix] != box_of_cell [ref_ix])
				{
					// obj_ix cell was already in a box, but it is also close to a cell in another box, so these boxes must be merged
					
					compl_box_merge (&temp_box [box_of_cell [obj_ix]], &temp_box [box_of_cell [ref_ix]]);
					if (!compl_box_within_limit (&temp_box [box_of_cell [ref_ix]]))
						return fail_code;
					
					delete_compl_box (box_of_cell [obj_ix], box_of_cell [ref_ix]);
				}
			}
		}
		
		if (box_of_cell [obj_ix] == -1)
		{
			// obj_ix cell was not close to a cell in an existing box, so start a new box and put it there
			if (box_cnt >= MAX_MAX_UNMERGED_LOCAL_RECTS)
			{
				fprintf (stderr, "Unmerged local rectangles buffer overflow\n");
				exit (-1);
			}
			
			compl_box_init (&temp_box [box_cnt], free_cells, max_compl);
			compl_box_add_cell (&temp_box [box_cnt], onlist_x [obj_ix], onlist_y [obj_ix]);
			box_of_cell [obj_ix] = box_cnt;
			box_cnt++;
		}
	}
	
	// Here we should first try to merge boxes to reduce the number of boxes and/or the total complexity of them
	
	if (box_cnt > max_local_rects)
		return COMPL_FAILED_TOO_MANY_RECTS;
	
	if (max_overall_local_compl != PARM_DISABLED)
	{
		int overall_compl = 0;
		int box_ix;
		for (box_ix = 0; box_ix < box_cnt; box_ix++)
			overall_compl += compl_box_size_compl (&temp_box [box_ix]);
		
		overall_compl += highest_of (0, onlist_cnt - LOCAL_COMPL_OVERALL_FREE_CELLS);
		if (overall_compl > max_overall_local_compl)
			return COMPL_FAILED_OVERALL_LOCALLY;
	}
	
	return COMPL_OK;
}

static compl_result test_compl ()
{
	if (max_local_rect_compl != PARM_DISABLED || max_overall_local_compl != PARM_DISABLED)
	{
		compl_result loc_result = test_compl_locally ();
		if (loc_result != COMPL_OK)
			return loc_result;
	}
	
	if (max_global_compl != PARM_DISABLED)
	{
		compl_box_init (&temp_box [0], GLOBAL_COMPL_FREE_CELLS, max_global_compl);
		
		int cell_ix;
		for (cell_ix = 0; cell_ix < onlist_cnt; cell_ix++)
		{
			compl_box_add_cell (&temp_box [0], onlist_x [cell_ix], onlist_y [cell_ix]);
			if (!compl_box_within_limit (&temp_box [0]))
				return COMPL_FAILED_GLOBALLY;
		}
	}
		
	return COMPL_OK;
}


static void bellman_choose_cells (universe *u, generation *g, int allow_new_oncells, int first_gen_with_unknown_cells, int first_next_sol_gen)
{
	// Look for a tile with some unknown cells.
	
	g = u_evolving->first;
	
	tile *t;
	do {
		for(t = g->all_first;
			t && !(t->flags & HAS_UNKNOWN_CELLS);
			t = t->all_next)
			;
		if(!t) g = g->next;
	} while(g && !t);
	
	if(!g)
	{
		// We got all the way to the end of the pattern. This should not happen anymore - all
		// solutions should be found before here and anything else should already be pruned
		// Remember and report when search completed
		
		got_to_end_of_pattern = YES;
		return;
	}
	
	// Find an unknown successor cell that's in the neighbourhood
	// of an unknown-stable predecessor cell.
	
	assert_if_debug(t->prev != NULL);
	
	int x, y, dx = 2, dy = 2;
	
	// Look for direct predecessors first ...
	
	for(y=0; y<TILE_HEIGHT; y++) {
		TILE_WORD is_unk = 0;
		is_unk = t->bit1[y] & ~t->bit0[y];
		if(is_unk) {
			for(x = 0; x < TILE_WIDTH; x++) {
				if((is_unk >> x) & 1) {
					assert_if_debug(tile_get_cell(t, x, y) == UNKNOWN);
					// Now look for an unknown-stable cell near it.
					if((x == 0) || (x == TILE_WIDTH-1) || (y == 0) || (y == TILE_HEIGHT-1)) {
						fprintf(stderr, "TODO: handle tile wrap! (%d, %d, %d)\n", g->gen, x, y);
						assert(0);
					}
					
					
					TRY(0, 0);
				}
			}
			
		}
	}
	
	// ... then orthogonally adjacent cells ...
	
	for(y=0; y<TILE_HEIGHT; y++) {
		TILE_WORD is_unk = 0;
		is_unk = t->bit1[y] & ~t->bit0[y];
		if(is_unk) {
			for(x = 0; x < TILE_WIDTH; x++) {
				if((is_unk >> x) & 1) {
					assert_if_debug(tile_get_cell(t, x, y) == UNKNOWN);
					// Now look for an unknown-stable cell near it.
					if((x == 0) || (x == TILE_WIDTH-1) || (y == 0) || (y == TILE_HEIGHT-1)) {
						fprintf(stderr, "TODO: handle tile wrap! (%d, %d, %d)\n", g->gen, x, y);
						assert(0);
					}
					
					
					TRY(1, 0);
					TRY(0, 1);
					TRY(-1, 0);
					TRY(0, -1);
				}
			}
			
		}
	}
	
	// ... then diagonally adjacent ones.
	
	for(y=0; y<TILE_HEIGHT; y++) {
		TILE_WORD is_unk = 0;
		is_unk = t->bit1[y] & ~t->bit0[y];
		if(is_unk) {
			for(x = 0; x < TILE_WIDTH; x++) {
				if((is_unk >> x) & 1) {
					assert_if_debug(tile_get_cell(t, x, y) == UNKNOWN);
					// Now look for an unknown-stable cell near it.
					if((x == 0) || (x == TILE_WIDTH-1) || (y == 0) || (y == TILE_HEIGHT-1)) {
						fprintf(stderr, "TODO: handle tile wrap! (%d, %d, %d)\n", g->gen, x, y);
						assert(0);
					}
					
					
					TRY(-1, -1);
					TRY(-1, 1);
					TRY(1, -1);
					TRY(1, 1);
				}
			}
			
		}
	}
		
	fprintf(stderr, "Didn't find an unknown cell!\n");
	assert(0);
	return;
	
found:
	assert_if_debug(tile_get_cell(t, x, y) == UNKNOWN);
	assert_if_debug(tile_get_cell(t->prev, x+dx, y+dy) == UNKNOWN_STABLE);
	assert_if_debug(tile_get_cell((tile *)t->auxdata, x+dx, y+dy) == UNKNOWN_STABLE);
	
	assert_if_debug(dx <= 1);
	assert_if_debug(dy <= 1);
	x += dx;
	y += dy;
	
	int xmirror[8], ymirror[8], n_sym, i;
	
	n_sym = xy_symmetry(x, y, xmirror, ymirror);
	
	for(i = 0; i < n_sym; i++) {
		if(tile_get_cell(t->prev, xmirror[i], ymirror[i]) != UNKNOWN_STABLE) {
			fprintf(stderr, "Input region is asymmetric (%d,%d)=%d (%d,%d)=%d\n",
					x, y, tile_get_cell(t->prev, x, y),
					xmirror [i], ymirror [i], tile_get_cell(t->prev, xmirror [i], ymirror [i]));
			exit(-1);
		}
	}
	
	
	// Recurse with the selected cell as ON
	if (allow_new_oncells)
	{
		if (max_added_static_on == PARM_DISABLED || onlist_cnt + n_sym <= max_added_static_on)
		{
			if (onlist_cnt + n_sym > MAX_MAX_ADDED_STATIC_ON)
			{
				fprintf (stderr, "On-cell list overflow\n");
				assert (0);
			}
			
			for(i = 0; i < n_sym; i++)
			{
				onlist_x [onlist_cnt] = xmirror [i];
				onlist_y [onlist_cnt] = ymirror [i];
				onlist_cnt++;
			}
			
			compl_result cr = test_compl ();
			if (cr == COMPL_OK)
			{
				for(i = 0; i < n_sym; i++){
					tile_set_cell(t->prev,  xmirror[i], ymirror[i], ON);
					tile_set_cell((tile *)t->auxdata,  xmirror[i], ymirror[i], ON);
				}
				
				g->prev->flags |= CHANGED;
				
				bellman_recurse(u, g->prev, allow_new_oncells, first_gen_with_unknown_cells, first_next_sol_gen);
			}
			else if (cr == COMPL_FAILED_LOCAL_RECT)
				prune_too_compl_local_rect++;
			else if (cr == COMPL_FAILED_OVERALL_LOCALLY)
				prune_too_compl_overall_locally++;
			else if (cr == COMPL_FAILED_TOO_MANY_RECTS)
				prune_too_many_local_rects++;
			else if (cr == COMPL_FAILED_GLOBALLY)
				prune_too_compl_globally++;
			
			onlist_cnt -= n_sym;
			
		}
		else
			prune_too_many_added_static_on++;
	}
	else
		prune_stopped_adding_oncells++;
	
	
	// Recurse with the selected cell as OFF
	for(i = 0; i < n_sym; i++){
		tile_set_cell(t->prev,  xmirror[i], ymirror[i], OFF);
		tile_set_cell((tile *)t->auxdata,  xmirror[i], ymirror[i], OFF);
	}
	
	g->prev->flags |= CHANGED;
	
	bellman_recurse(u, g->prev, allow_new_oncells, first_gen_with_unknown_cells, first_next_sol_gen);
	
	for(i = 0; i < n_sym; i++){
		tile_set_cell(t->prev,  xmirror[i], ymirror[i], UNKNOWN_STABLE);
		tile_set_cell((tile *)t->auxdata,  xmirror[i], ymirror[i], UNKNOWN_STABLE);
	}
	
	g->prev->flags |= CHANGED;
}

int main(int argc, char *argv[]) {
	
	enum {
			SEARCH,
			CLASSIFY
	} mode = SEARCH;
	int verbose = 0;
	
	start_time = time (NULL);
	
	u_static = universe_new(OFF);
	u_evolving = universe_new(OFF);
	u_forbidden = universe_new(OFF);
	u_filter = universe_new(UNKNOWN);
	
	int c;
	
	while((c = getopt(argc, argv, "cv")) != -1) switch(c) {
		case 'c':
			mode = CLASSIFY;
			break;
			
		case 'v': verbose++; break;
	}
	
	FILE *f = fopen(argv[optind], "r");
	if(!f) {
		perror(argv[optind]);
		return -1;
	}
	
	if (!read_life105(f, read_cb, read_param_cb, NULL))
		exit (-1);
	
	fclose(f);
	
	if (!verify_and_fix_parameters ())
		exit (-1);
	
	if (accept1_inact_gens == PARM_DISABLED)
		max_gens = max_last_act_gen + (accept2_act_inact_gens - 1) + 1;
	else if (accept2_act_inact_gens == PARM_DISABLED)
		max_gens = max_last_act_gen + accept1_inact_gens + 1;
	else
		max_gens = lowest_of (max_last_act_gen + (accept2_act_inact_gens - 1) + 1, max_last_act_gen + accept1_inact_gens + 1);

	max_gens = highest_of (max_gens, u_filter->n_gens + 1);
	
	universe_evolve_next(u_static);
	
	int i;
	int x, y;
	generation *g;
	tile *t, *tp;
	
	g = universe_find_generation(u_static, 0, 0);
	for(t = g->all_first; t; t = t->all_next) {
		tile *t2 = universe_find_tile(u_forbidden, 0, t->xpos, t->ypos, 0);
		if(t2) t->auxdata = t2;
	}
	
	for(i=0; i<max_gens; i++) {
		universe_evolve_next(u_evolving);
		
		g = universe_find_generation(u_evolving, i, 0);
		for(t = g->all_first; t; t = t->all_next) {
			tile *t2 = universe_find_tile(u_static, 0, t->xpos, t->ypos, 0);
			if(t2) t->auxdata = t2;
			
			t2 = universe_find_tile(u_filter, g->gen + 1, t->xpos, t->ypos, 0);
			if(t2) t->filter = t2;
		}
	}
	
	/* set auxdata in the final generation: */
	g = universe_find_generation(u_evolving, i, 0);
	for(t = g->all_first; t; t = t->all_next) {
		tile *t2 = universe_find_tile(u_static, 0, t->xpos, t->ypos, 0);
		if(t2) t->auxdata = t2;
		t->filter = NULL;
	}
	
	bellman_evolve_generations(u_evolving->first, max_gens);
	
	int ac_first, ac_last;
	uint32_t klass;
	
	switch(mode) {
		case SEARCH:
			printf ("=== %s, %s ===\n", program_name, version_string);
			if (!verify_static_is_stable ())
			{
				fprintf (stderr, "Predefined static pattern is not stable\n");
				exit (-1);
			}
			
			printf ("--- Starting search, max generations = %d\n", max_gens);
			
			// This used to be a call to bellman_choose_cells, but now we start at bellman_recurse instead
			// because we don't know yet if there are any unknown cells
			
			if (strictly_gen_by_gen)
			{
				int sg;
				for (sg = min_first_act_gen; sg <= max_first_act_gen; sg++)
				{
					last_new_gen_time = time (NULL);
					printf ("\n--- Starting generation %d\n", sg);
					current_single_gen = sg;
					bellman_recurse (u_evolving, u_evolving->first, YES, 0, 0);
				}
			}
			else
				bellman_recurse (u_evolving, u_evolving->first, YES, 0, 0);
			
			print_prune_counters (YES);
			
			if (got_to_end_of_pattern)
			{
				fprintf (stderr, "\n\n");
				fprintf (stderr, "=== Warning: At some point Bellman_szlim got to the last generation while\n");
				fprintf (stderr, "             searching. This corresponds to the Type 1 solutions of\n");
				fprintf (stderr, "             previous Bellman versions. The search continued with no\n");
				fprintf (stderr, "             adverse effects, but this really shouldn't happen anymore.\n");
				fprintf (stderr, "=== Please report this as a bug!\n");
				fprintf (stderr, "=== Supply the input file and state the version number ""%s""\n\n", version_string);
			}
			break;
			
		case CLASSIFY:
			
			if(verbose > 0) {
				if(verbose > 1)
					dump(YES);
				for(g = u_evolving->first; g; g = g->next) {
					printf("Generation %d: %x: %s\n", g->gen, g->flags, flag2str(g->flags));
				}
				
			}
			
			// print the history
			int in_interaction = 0, interaction_nr = 0;
			
			for(g = u_evolving->first->next; g; g = g->next) {
				if(!(g->flags & IS_LIVE)) {
					printf("log: g%d: died out\n", g->gen);
					break;
				}
				if(g->flags & HAS_UNKNOWN_CELLS) {
					printf("log: g%d: became undetermined\n", g->gen);
					break;
				}
				if(!(g->flags & DIFFERS_FROM_PREVIOUS)) {
					printf("log: g%d: became stable\n", g->gen);
					break;
				}
				if(!(g->flags & DIFFERS_FROM_2PREV)) {
					printf("log: g%d: became period 2\n", g->gen);
					break;
				}
				
				if(!in_interaction) {
					if(g->flags & DIFFERS_FROM_STABLE) {
						interaction_nr++;
						in_interaction = 1;
						printf("log: g%d: interaction %d begins\n",
							   g->gen, interaction_nr);
					}
				} else {
					if(!(g->flags & DIFFERS_FROM_STABLE)) {
						in_interaction = 0;
						printf("log: g%d: interaction %d ends\n",
							   g->gen, interaction_nr);
					}
				}
			}
			
			// find the first active generation
			for(g = u_evolving->first; g && !(g->flags & DIFFERS_FROM_STABLE); g = g->next)
				;
			generation *g_last;
			
			if(!g) {
				klass = 0;
				goto done;
			}
			ac_first = g->gen;
			if(verbose > 0)
				printf("First active generation: %d\n", ac_first);
			
			// find the generation after the last active generation
			g_last = g;
			for(; g; g = g->next) {
				if(g->flags & DIFFERS_FROM_STABLE)
					g_last = g;
			}
			
			if(!g_last) {
				klass = 1;
				goto done;
			}
			
			g = g_last->next ? g_last->next : g_last;
			ac_last = g->gen;
			if(verbose > 0)
				printf("Last active generation: %d\n", ac_last);
			
			klass = (2 * ac_first) + (3 * ac_last);
			
			// The catalyst has returned to its stable state. Any
			// remaining differences are the generated spark.
			
			// We calculate a hash for each tile independently,
			// and sum them; this way the result is independent of
			// the order in which we traverse the tiles.
			
			for(t = g->all_first; t; t = t->all_next) {
				uint32_t hash = 1;
				tp = universe_find_tile(u_static, 0, t->xpos, t->ypos, 1);
				for(y=0; y<TILE_HEIGHT; y++) for(x=0; x<TILE_WIDTH; x++) {
					cellvalue t1 = tile_get_cell(t, x, y);
					cellvalue t2 = tile_get_cell(tp, x, y);
					if(t1 != t2) {
						hash = (hash ^ t1) * 0xabcdef13;
						hash = (hash ^ t2) * 0xabcdef13;
						hash = (hash ^ x) * 0xabcdef13;
						hash = (hash ^ y) * 0xabcdef13;
					}
				}
				klass += hash;
			}

done:
			printf("hash: %08x\n", klass);
			break;
	}
	return 0;
}
