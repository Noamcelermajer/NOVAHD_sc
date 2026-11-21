/* Windows/Linux host runner: loads the image, sets up the Objective-C runtime and the frameworks, runs the
 * static constructors and the game's main().
 *
 *   novahd_runner <NovaHD.app folder> [--image image.bin] [--home folder] [-v|-vv|-vvv]
 *
 * The game sees its bundle at /var/mobile/Applications/NOVAHD/NovaHD.app and its home (Documents, Library) at
 * /var/mobile/Applications/NOVAHD; both map to host folders.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "rt.h"

#define GAME_HOME "/var/mobile/Applications/NOVAHD"
#define GAME_BUNDLE GAME_HOME "/NovaHD.app"

void rt_objc_define_root(void);

int main(int argc, char **argv) {
    const char *app = NULL, *image = "image.bin", *home = "home";
    for (int k = 1; k < argc; k++) {
        if (!strcmp(argv[k], "--image") && k + 1 < argc) image = argv[++k];
        else if (!strcmp(argv[k], "--home") && k + 1 < argc) home = argv[++k];
        else if (!strncmp(argv[k], "-v", 2)) rt_verbose = (int)strlen(argv[k]) - 1;
        else app = argv[k];
    }
    if (!app) {
        fprintf(stderr, "usage: %s <NovaHD.app folder> [--image image.bin] [--home folder] [-v]\n", argv[0]);
        return 2;
    }
    snprintf(rt_bundle_path, sizeof rt_bundle_path, "%s", GAME_BUNDLE);
    snprintf(rt_home_path, sizeof rt_home_path, "%s", GAME_HOME);
    rt_path_alias(GAME_BUNDLE, app);
    rt_path_alias(GAME_HOME, home);

    rt_mem_init(image);
    /* classes first (the data imports point at them), then the imports and their data, then the game's classes */
    rt_objc_define_root();
    rt_foundation_define();
    rt_uikit_define();
    rt_imports_init();
    rt_data_imports_bind();
    rt_objc_init();

    cpu_t *c = rt_thread_cpu();
    rt_objc_load();
    for (uint32_t k = 0; k < rt_init_func_count; k++) {
        rt_call(c, rt_init_funcs[k], 0);
        if (c->fault) { rt_log("constructor %#x faulted (%u)", rt_init_funcs[k], c->fault); return 1; }
    }
    rt_log("%u static constructors done", rt_init_func_count);

    uint32_t argv0 = rt_static_string(GAME_BUNDLE "/NovaHD"), gargv = rt_calloc(2, 4);
    rt_st32(gargv, argv0);
    uint32_t r = rt_call(c, rt_main, 2, 1, gargv);
    rt_log("main returned %u (fault %u)", r, c->fault);
    return c->fault ? 1 : 0;
}
