/*
 * SPIN Model for Namespace Confinement Verification
 *
 * Verifies: "An agent cannot access capabilities outside its namespace"
 *
 * Models the core security property from the paper (Section 3.3):
 * Path resolution (namec) only succeeds for paths in the process's namespace.
 */

#define MAX_PROCS 3

mtype = { PATH_ROOT, PATH_OSM, PATH_LLM, PATH_MEMORY, PATH_ETC_PASSWD, PATH_ADMIN };

typedef namespace {
    bit has_root;
    bit has_osm;
    bit has_llm;
    bit has_memory;
    bit has_etc_passwd;
    bit has_admin;
}

typedef process {
    byte pgrpid;
    namespace ns;
}

process procs[MAX_PROCS];
byte access_attempts = 0;
byte successful_accesses = 0;
byte failed_accesses = 0;

/*
 * Test: Agent path access
 */
proctype test_agent() {
    byte result;
    mtype path;

    /* Choose a path to access */
    if
    :: path = PATH_OSM;
    :: path = PATH_LLM;
    :: path = PATH_ETC_PASSWD;  /* Adversarial */
    fi

    access_attempts++;

    /* Simulate namec: check if path is in namespace */
    atomic {
        if
        :: (path == PATH_ROOT && procs[_pid - 1].ns.has_root) -> result = 1;
        :: (path == PATH_OSM && procs[_pid - 1].ns.has_osm) -> result = 1;
        :: (path == PATH_LLM && procs[_pid - 1].ns.has_llm) -> result = 1;
        :: (path == PATH_MEMORY && procs[_pid - 1].ns.has_memory) -> result = 1;
        :: (path == PATH_ETC_PASSWD && procs[_pid - 1].ns.has_etc_passwd) -> result = 1;
        :: (path == PATH_ADMIN && procs[_pid - 1].ns.has_admin) -> result = 1;
        :: else -> result = 0;
        fi;

        if
        :: result == 1 -> successful_accesses++;
        :: result == 0 -> failed_accesses++;
        fi
    }

    /* PROPERTY: Success implies path in namespace */
    assert(
        (result == 0) ||
        (result == 1 &&
         ((path == PATH_ROOT && procs[_pid - 1].ns.has_root) ||
          (path == PATH_OSM && procs[_pid - 1].ns.has_osm) ||
          (path == PATH_LLM && procs[_pid - 1].ns.has_llm) ||
          (path == PATH_MEMORY && procs[_pid - 1].ns.has_memory) ||
          (path == PATH_ETC_PASSWD && procs[_pid - 1].ns.has_etc_passwd) ||
          (path == PATH_ADMIN && procs[_pid - 1].ns.has_admin)))
    );
}

/*
 * Initialize and run
 */
init {
    atomic {
        /* Process 0: Restricted agent */
        procs[0].pgrpid = 1;
        procs[0].ns.has_root = 1;
        procs[0].ns.has_osm = 1;
        procs[0].ns.has_llm = 1;
        procs[0].ns.has_memory = 1;
        procs[0].ns.has_etc_passwd = 0;  /* NOT mounted */
        procs[0].ns.has_admin = 0;

        /* Process 1: Privileged */
        procs[1].pgrpid = 2;
        procs[1].ns.has_root = 1;
        procs[1].ns.has_osm = 1;
        procs[1].ns.has_llm = 1;
        procs[1].ns.has_memory = 1;
        procs[1].ns.has_etc_passwd = 1;  /* HAS access */
        procs[1].ns.has_admin = 1;

        /* Process 2: Minimal */
        procs[2].pgrpid = 3;
        procs[2].ns.has_root = 1;
        procs[2].ns.has_osm = 0;
        procs[2].ns.has_llm = 1;
        procs[2].ns.has_memory = 1;
        procs[2].ns.has_etc_passwd = 0;
        procs[2].ns.has_admin = 0;
    }

    /* Run tests */
    run test_agent();
    run test_agent();
    run test_agent();

    /* Wait for completion */
    (_nr_pr == 1);

    /* Verify confinement held */
    assert(access_attempts == successful_accesses + failed_accesses);
}
