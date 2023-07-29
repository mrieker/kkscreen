/**
 * Usable version of screen.
 */

//    Copyright (C) 2014, Mike Rieker, Beverly, MA USA
//    www.outerworldapps.com
//
//    This program is free software; you can redistribute it and/or modify
//    it under the terms of the GNU General Public License as published by
//    the Free Software Foundation; version 2 of the License.
//
//    This program is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//    GNU General Public License for more details.
//
//    EXPECT it to FAIL when someone's HeALTh or PROpeRTy is at RISk.
//
//    You should have received a copy of the GNU General Public License
//    along with this program; if not, write to the Free Software
//    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
//
//    http://www.gnu.org/licenses/gpl-2.0.html

// cc -Wall -Werror -O2 -o kkscreen kkscreen.c -lpthread -lutil

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <pty.h>
#include <pwd.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>

#define ENDCHAR (']'-'@')
#define FALSE 0
#define TRUE 1

typedef struct Inbound Inbound;
typedef struct Screen Screen;

static char const *endmsg = "\r\nkkscreen: user process terminated\r\n";
static char do_list_filter_param[24];
static int volatile gotsigwinch;
struct sockaddr_un crsockaddr;

static int cmd_attach (int argc, char **argv);
static int do_attach (char *name, char endch, char *until, FILE *logfile);
static void handle_sigwinch (int sig);
static void update_winsize (int sockfd);
static int cmd_create (int argc, char **argv);
static int unlink_unused (char const *name);
static void handle_abortsig (int sig);
static void *accept_thread (void *screenv);
static int accept_inbound (Screen *screen);
static int handle_screen (Screen *screen);
static void *connection_thread (void *inboundv);
static void incoming_command (Inbound *inbound, char *buf, int len);
static int cmd_inject (int argc, char **argv);
static void flushpipereads (int fd);
static void unusedint (int rc);
static int cmd_kill (int argc, char **argv);
static void do_kill (char const *name);
static int cmd_list (int argc, char **argv);
static void do_list (int myuid);
static int do_list_filter (struct dirent const *de);
static int outbound_connect (char const *name);
static int get_sock_name (struct sockaddr_un *sa, char const *name);
static int readpipe (int fd, char *buf, int len);
static int writepipe (int fd, char const *buf, int len);


int main (int argc, char **argv)
{
    if (signal (SIGPIPE, SIG_IGN) == SIG_ERR) abort ();

    if (argc < 2) goto usage;
    if (strcasecmp (argv[1], "attach") == 0) return cmd_attach (argc - 1, argv + 1);
    if (strcasecmp (argv[1], "create") == 0) return cmd_create (argc - 1, argv + 1);
    if (strcasecmp (argv[1], "inject") == 0) return cmd_inject (argc - 1, argv + 1);
    if (strcasecmp (argv[1], "kill")   == 0) return cmd_kill   (argc - 1, argv + 1);
    if (strcasecmp (argv[1], "list")   == 0) return cmd_list   (argc - 1, argv + 1);

usage:
    fprintf (stderr, "usage: kkscreen attach ...\n");
    fprintf (stderr, "       kkscreen create ...\n");
    fprintf (stderr, "       kkscreen inject ...\n");
    fprintf (stderr, "       kkscreen kill ...\n");
    fprintf (stderr, "       kkscreen list ...\n");
    fprintf (stderr, "    sessionname can be a simple name and is owned by the calling user\n");
    fprintf (stderr, "    or it can be <uid>/<simplename> and is owned by the given uid\n");
    fprintf (stderr, "    or it can be <username>/<simplename> and is owned by the given user's uid\n");
    return 1;
}

/**************************\
 *  attach <sessionname>  *
\**************************/

static int cmd_attach (int argc, char **argv)
{
    char endch, *name, *p, *until;
    FILE *logfile;
    int i;
    long chrcode;

    endch = ENDCHAR;
    logfile = NULL;
    name = NULL;
    until = NULL;

    for (i = 0; ++ i < argc;) {
        if (argv[i][0] == '-') {
            if (strcasecmp (argv[i], "-endchar") == 0) {
                if (++ i >= argc) {
                    fprintf (stderr, "kkscreen: missing endchar arg\n");
                    goto usage;
                }
                endch = argv[i][0];
                if ((endch >= 0x40) && (endch <= 0x7F) && (argv[i][1] == 0)) {
                    endch &= 0x1F;
                    continue;
                }
                if ((endch >= '0') && (endch <= '9')) {
                    chrcode = strtol (argv[i], &p, 0);
                    if ((*p == 0) && (chrcode >= 0) && (chrcode <= 255)) {
                        endch = chrcode;
                        continue;
                    }
                }
                fprintf (stderr, "kkscreen: bad endchar %s\n", argv[i]);
                goto usage;
            }
            if (strcasecmp (argv[i], "-logfile") == 0) {
                if (++ i >= argc) {
                    fprintf (stderr, "kkscreen: missing logfile arg\n");
                    goto usage;
                }
                logfile = fopen (argv[i], "w");
                if (logfile == NULL) {
                    fprintf (stderr, "kkscreen: eeror creating logfile %s: %s\n", argv[i], strerror (errno));
                    return -1;
                }
                continue;
            }
            if (strcasecmp (argv[i], "-until") == 0) {
                if (++ i >= argc) {
                    fprintf (stderr, "kkscreen: missing until arg\n");
                    goto usage;
                }
                until = argv[i];
                continue;
            }
            fprintf (stderr, "kkscreen: unknown option %s\n", argv[i]);
            goto usage;
        }
        if (name != NULL) {
            fprintf (stderr, "kkscreen: unknown argument %s\n", argv[i]);
            goto usage;
        }
        name = argv[i];
    }
    if (name == NULL) {
        fprintf (stderr, "kkscreen: missing <sessionname>\n");
        goto usage;
    }

    return do_attach (name, endch, until, logfile);

usage:
    fprintf (stderr, "usage: kkscreen attach [-endchar <ctrlchar>] [-logfile <filename>] [-until <string>] <sessionname>\n");
    fprintf (stderr, "       -endchar can have a single letter (or anything in ascii 0x40-0x7F)\n");
    fprintf (stderr, "           to indicate the corresponding control character\n");
    fprintf (stderr, "           eg, -endchar e  means control-e\n");
    fprintf (stderr, "           or can be a numeric value in range 0..255\n");
    fprintf (stderr, "           to indicate that character\n");
    fprintf (stderr, "           eg, -endchar 0x7E means ~\n");
    fprintf (stderr, "       default for -endchar is ctrl-%c\n", ENDCHAR + '@');
    fprintf (stderr, "       -until will terminate the attach when the string is seen\n");
    return 1;
}

static int do_attach (char *name, char endch, char *until, FILE *logfile)
{
    char buf[4096], *p, screenlinebuf[4096];
    fd_set readmask;
    int len, nfds, ofs, overage, rc, screenlinelen, sockfd;
    sigset_t newsigmask, oldsigmask;
    struct termios newtermios, oldtermios;

    screenlinelen = 0;

    /*
     * Open connection to server.
     */
    sockfd = outbound_connect (name);
    if (sockfd < 0) {
        if (sockfd != -999999999) fprintf (stderr, "kkscreen: connect(%s) error: %s\n", name, strerror (-sockfd));
        return 2;
    }

    /*
     * Save local terminal characteristics and set it to raw mode.
     */
    if (tcgetattr (STDIN_FILENO, &oldtermios) < 0) {
        fprintf (stderr, "kkscreen: tcgetattr() error: %s\n", strerror (errno));
        rc = 2;
        goto done2;
    }

    newtermios = oldtermios;
    cfmakeraw (&newtermios);

    if (tcsetattr (STDIN_FILENO, TCSAFLUSH, &newtermios) < 0) {
        fprintf (stderr, "kkscreen: tcsetattr() error: %s\n", strerror (errno));
        rc = 2;
        goto done2;
    }

    /*
     * Get changes to window size and send current size to server.
     * Set up signal masks such that SIGWINCH can be handled only while in pselect()
     * so it will be sure to break out of pselect().
     */
    sigemptyset (&newsigmask);
    sigaddset (&newsigmask, SIGWINCH);
    if (sigprocmask (SIG_BLOCK, &newsigmask, &oldsigmask) < 0) abort ();

    if (signal (SIGWINCH, handle_sigwinch) < 0) abort ();

    update_winsize (sockfd);

    /*
     * Shuttle data back and forth.
     */
    nfds = sockfd + 1;
    while (TRUE) {
        FD_ZERO (&readmask);
        FD_SET (STDIN_FILENO, &readmask);
        FD_SET (sockfd, &readmask);
        rc = pselect (nfds, &readmask, NULL, NULL, NULL, &oldsigmask);
        if ((rc < 0) && (errno != EINTR)) {
            fprintf (stderr, "kkscreen: select() error: %s\n", strerror (errno));
            rc = 2;
            goto done1;
        }

        /*
         * If local window size has changed, tell server.
         */
        if (gotsigwinch) {
            gotsigwinch = FALSE;
            update_winsize (sockfd);
        }

        /*
         * The readmask flags are valid only if not interrupted.
         */
        if (rc < 0) continue;

        /*
         * Send local keyboard data over link to user process.
         */
        if (FD_ISSET (STDIN_FILENO, &readmask)) {
            rc = read (STDIN_FILENO, buf + 1, sizeof buf - 1);
            if (rc <= 0) {
                if (rc < 0) {
                    fprintf (stderr, "kkscreen: read() stdin error: %s\n", strerror (errno));
                    rc = 2;
                }
                goto done1;
            }
            if (memchr (buf + 1, endch, rc) != NULL) {
                writepipe (STDOUT_FILENO, "\r\n", 2);
                rc = 0;
                goto done1;
            }
            for (ofs = 0; (len = rc - ofs) > 0; ofs += len) {
                if (len > 128) len = 128;
                buf[ofs] = len - 1;
                if (!writepipe (sockfd, buf + ofs, len + 1)) {
                    fprintf (stderr, "kkscreen: write() pipe error: %s\n", strerror (errno));
                    rc = 2;
                    goto done1;
                }
            }
        }

        /*
         * Get user process data from link and display on local screen.
         */
        if (FD_ISSET (sockfd, &readmask)) {

            /*
             * Read from user process' output pipe.
             */
            rc = read (sockfd, buf, sizeof buf);
            if (rc <= 0) {
                if (rc < 0) {
                    fprintf (stderr, "kkscreen: read() pipe error: %s\n", strerror (errno));
                    rc = 2;
                }
                goto done1;
            }

            /*
             * Send it to our stdout.
             */
            if (!writepipe (STDOUT_FILENO, buf, rc)) {
                fprintf (stderr, "kkscreen: write() stdout error: %s\n", strerror (errno));
                rc = 2;
                goto done1;
            }

            /*
             * Maybe write to log file.
             */
            if (logfile != NULL) {
                fwrite (buf, rc, 1, logfile);
            }

            /*
             * See if we are looking for an 'until' string.
             */
            if (until != NULL) {

                /*
                 * Ok, accumulate in latest screen line buffer.
                 */
                overage = screenlinelen + rc - sizeof screenlinebuf;
                if (overage > 0) {
                    screenlinelen -= overage;
                    if (screenlinelen < 0) abort ();
                    memmove (screenlinebuf, screenlinebuf + overage, screenlinelen);
                }
                memcpy (screenlinebuf + screenlinelen, buf, rc);
                screenlinelen += rc;

                /*
                 * See if we now have a full line (indicated by a \n in buffer).
                 */
                p = memchr (buf, '\n', rc);
                if (p != NULL) {

                    /*
                     * Nul terminate the line we have and see if it matches the until.
                     */
                    p += (screenlinebuf + screenlinelen) - (buf + rc);
                    *p = 0;
                    if (strstr (screenlinebuf, until) != NULL) {
                        writepipe (STDOUT_FILENO, "\r\n", 2);
                        rc = 0;
                        goto done1;
                    }

                    /*
                     * Doesn't match, strip line from line buffer and keep going.
                     */
                    screenlinelen -= ++ p - screenlinebuf;
                    memmove (screenlinebuf, p, screenlinelen);
                }
            }
        }
    }

done1:
    if (tcsetattr (STDIN_FILENO, TCSAFLUSH, &oldtermios) < 0) {
        fprintf (stderr, "kkscreen: tcsetattr() error: %s\n", strerror (errno));
        if (rc == 0) rc = 2;
    }
done2:
    close (sockfd);
    if (logfile != NULL) fclose (logfile);
    return rc;
}


/**
 * @brief Signal caught when local window changes size.
 */
static void handle_sigwinch (int sig)
{
    gotsigwinch = TRUE;
}


/**
 * @brief Send current window size to the server.
 */
static void update_winsize (int sockfd)
{
    char buf[16];
    int len;
    struct winsize winsz;

    if (ioctl (STDOUT_FILENO, TIOCGWINSZ, &winsz) < 0) {
        fprintf (stderr, "kkscreen: ioctl(TIOCGWINSZ) error: %s\n", strerror (errno));
    } else {
        len = snprintf (buf + 1, sizeof buf - 1, "ws:%u:%u", winsz.ws_col, winsz.ws_row);
        buf[0] = -len;
        writepipe (sockfd, buf, len + 1);
    }
}

/***************************************\
 *  create <sessionname> <command>...  *
\***************************************/

struct Inbound {
    Inbound *next;          // next on screen->inbounds list
    Screen *screen;         // which screen we are part of
    int confd;              // connection fd
    int writebad;           // write() to confd was bad
    int lastwidth;          // latest width set
    int lastheight;         // latest height set
};

struct Screen {
    Inbound *inbounds;      // list of current inbound connections
    pthread_mutex_t mutex;  // lock ring buffer and inbounds list
    int lisfd;              // listening socket fd
    int ptyfd;              // pseudo-terminal backside fd
    int curwidth;           // current width set
    int curheight;          // current height set
    int insert;             // where to insert next in buf[]
    int wrapped;            // bool indicating 'insert' has wrapped
    int waitfds[2];         // pipe to wait for first attach
    char buf[16000];        // last 16000 chars from user process
};


static int cmd_create (int argc, char **argv)
{
    char *name;
    int command, exstat, oldmask, opt_daemon, opt_force, opt_wait, pid, rc, uid;
    pthread_t inbound_thread;
    Screen screen;
    struct winsize winsz;

    memset (&screen, 0, sizeof screen);
    pthread_mutex_init (&screen.mutex, NULL);
    screen.lisfd = -1;
    screen.ptyfd = -1;
    screen.waitfds[0] = -1;
    screen.waitfds[1] = -1;

    if (!isatty (STDOUT_FILENO) || (ioctl (STDOUT_FILENO, TIOCGWINSZ, &winsz) < 0)) {
        memset (&winsz, 0, sizeof winsz);
        winsz.ws_col = 80;
        winsz.ws_row = 24;
    }

    /*
     * Decode command arguments.
     */
    name       = NULL;
    opt_daemon = FALSE;
    opt_force  = FALSE;
    opt_wait   = FALSE;
    for (command = 0; ++ command < argc;) {
        if (argv[command][0] == '-') {
            if (strcasecmp (argv[command], "-daemon") == 0) {
                opt_daemon = TRUE;
                continue;
            }
            if (strcasecmp (argv[command], "-force") == 0) {
                opt_force = TRUE;
                continue;
            }
            if (strcasecmp (argv[command], "-height") == 0) {
                if (++ command >= argc) goto usage;
                winsz.ws_row = atoi (argv[command]);
                continue;
            }
            if (strcasecmp (argv[command], "-wait") == 0) {
                opt_wait = TRUE;
                continue;
            }
            if (strcasecmp (argv[command], "-width") == 0) {
                if (++ command >= argc) goto usage;
                winsz.ws_col = atoi (argv[command]);
                continue;
            }
            fprintf (stderr, "kkscreen: unknown option %s\n", argv[command]);
            goto usage;
        }
        if (name != NULL) break;
        name = argv[command];
    }
    if (name == NULL) {
        fprintf (stderr, "kkscreen: missing <sessionname>\n");
        goto usage;
    }
    if (command >= argc) {
        fprintf (stderr, "kkscreen: missing <command>...\n");
        goto usage;
    }

    /*
     * Start listening on socket for the given name.
     */
    uid = get_sock_name (&crsockaddr, name);
    if (uid < 0) return 2;
    if (uid != geteuid ()) {
        fprintf (stderr, "kkscreen: cannot create socket belonging to another user\n");
        return 2;
    }

    screen.lisfd = socket (AF_UNIX, SOCK_STREAM, 0);
    if (screen.lisfd < 0) {
        fprintf (stderr, "kkscreen: socket() error: %s\n", strerror (errno));
        return 2;
    }

    oldmask = umask (0077);
bindit:
    if (bind (screen.lisfd, (void *)&crsockaddr, sizeof crsockaddr) < 0) {
        rc = errno;

        // if already in use but server is dead, get rid of old socket then retry
        if ((rc == EADDRINUSE) && unlink_unused (name)) goto bindit;

        // if already in use and server is alive, -force enables killing old server then retry
        if ((rc == EADDRINUSE) && opt_force) {
            opt_force = FALSE;
            do_kill (name);
            goto bindit;
        }

        // something else, fatal error
        fprintf (stderr, "kkscreen: bind(%s) error: %s\n", crsockaddr.sun_path, strerror (rc));
        umask (oldmask);
        rc = 2;
        goto done2;
    }
    umask (oldmask);

    if (listen (screen.lisfd, 5) < 0) {
        fprintf (stderr, "kkscreen: listen() error: %s\n", strerror (errno));
        rc = 2;
        goto done1;
    }

    /*
     * If -wait, set up synchronization pipes.
     * User process waits for something to be written to pipe before execing.
     * Server process writes to pipe when it has received first inbound connection.
     */
    if (opt_wait && (pipe (screen.waitfds) < 0)) abort ();

    /*
     * Create pseudo terminal and fork process to run user command.
     */
    screen.curwidth  = winsz.ws_col;
    screen.curheight = winsz.ws_row;
    pid = forkpty (&screen.ptyfd, NULL, NULL, &winsz);
    if (pid < 0) {
        fprintf (stderr, "kkscreen: fork() error: %s\n", strerror (errno));
        rc = 2;
        goto done1;
    }
    if (pid == 0) {
        close (screen.waitfds[1]);
        while ((read (screen.waitfds[0], &exstat, 1) < 0) && (errno == EINTR)) { }
        close (screen.waitfds[0]);
        execvp (argv[command], argv + command);
        fprintf (stderr, "kkscreen: execvp(%s) error: %s\n", argv[command], strerror (errno));
        exit (-1);
    }
    close (screen.waitfds[0]);
    screen.waitfds[0] = -1;

    /*
     * Maybe detach to run the server in a background process.
     */
    if (opt_daemon && (daemon (1, 0) < 0)) {
        fprintf (stderr, "kkscreen: daemon() error: %s\n", strerror (errno));
        rc = 2;
        goto done3;
    }

    /*
     * Delete socket if aborted via some signal.
     */
    if (signal (SIGHUP,  handle_abortsig) == SIG_ERR) abort ();
    if (signal (SIGINT,  handle_abortsig) == SIG_ERR) abort ();
    if (signal (SIGQUIT, handle_abortsig) == SIG_ERR) abort ();
    if (signal (SIGTERM, handle_abortsig) == SIG_ERR) abort ();
    if (signal (SIGUSR1, SIG_IGN) == SIG_ERR) abort ();
    if (signal (SIGUSR2, SIG_IGN) == SIG_ERR) abort ();

    /*
     * This thread accepts new inbound connections.
     */
    rc = pthread_create (&inbound_thread, NULL, accept_thread, &screen);
    if (rc != 0) {
        fprintf (stderr, "kkscreen: pthread_create() error: %s\n", strerror (rc));
        rc = 2;
        goto done3;
    }

    /*
     * Read screen data from user process and distribute to whoever wants it.
     * If we get an EOF, means the user process has exited so we do likewise.
     */
    rc = handle_screen (&screen);

    /*
     * Pass on process' exit status.
     */
    if ((rc == 0) && (waitpid (pid, &exstat, 0) > 0)) {
        rc = exstat;
        goto done1;
    }

done3:
    if (pid > 0) kill (pid, SIGKILL);
done1:
    unlink (crsockaddr.sun_path);
done2:
    close (screen.lisfd);
    return rc;

usage:
    fprintf (stderr, "usage: kkscreen create [-daemon] [-force] [-height <height>] [-wait] [-width <width>] <sessionname> <command>...\n");
    fprintf (stderr, "        -daemon : run server as a daemon\n");
    fprintf (stderr, "         -force : kill any existing same-named session\n");
    fprintf (stderr, "        -height : set pseudo-tty height\n");
    fprintf (stderr, "          -wait : user process waits for first attach\n");
    fprintf (stderr, "         -width : set pseudo-tty width\n");
    return 1;
}


/**
 * @brief If the socket already exists but the server is gone,
 *        unlink it so we can create a new one.
 */
static int unlink_unused (char const *name)
{
    char buf[256];
    int sockfd;

    /*
     * Try to open.
     */
    sockfd = outbound_connect (name);

    /*
     * If no socket there, it's already gone.
     */
    if (sockfd == -ENOENT) return TRUE;

    /*
     * If no server there, delete socket and now it's gone.
     */
    if (sockfd == -ECONNREFUSED) {
        unlink (crsockaddr.sun_path);
        return TRUE;
    }

    /*
     * If server there, tell it we're done with link.
     * Then tell caller we weren't able to delete socket.
     */
    if (sockfd >= 0) {
        shutdown (sockfd, SHUT_WR);
        while (read (sockfd, buf, sizeof buf) > 0) { }
        close (sockfd);
    }
    return FALSE;
}


/**
 * @brief Try to kill the socket if any abort-type signal then re-raise the signal.
 */
static void handle_abortsig (int sig)
{
    unlink (crsockaddr.sun_path);
    signal (sig, SIG_DFL);
    raise (sig);
}


/**
 * @brief This thread waits for inbound connections and creates another thread
 *        for each one to handle it.
 */
static void *accept_thread (void *screenv)
{
    int rc;
    Screen *screen;

    screen = screenv;
    while (TRUE) {
        rc = accept_inbound (screen);
        if (rc != 0) return (void *)(long)rc;
    }
}


/**
 * @brief Accept an inbound connection and create thread to handle it.
 */
static int accept_inbound (Screen *screen)
{
    Inbound *inbound;
    int confd, rc;
    pthread_t inbound_thread;
    socklen_t sockaddrlen;
    struct sockaddr_un sockaddr;

    /*
     * Wait for an inbound connection.
     */
    memset (&sockaddr, 0, sizeof sockaddr);
    sockaddrlen = sizeof sockaddr;
    confd = accept (screen->lisfd, (void *)&sockaddr, &sockaddrlen);
    if (confd < 0) {
        fprintf (stderr, "kkscreen: accept() error: %s\n", strerror (errno));
        return 0;
    }

    /*
     * Create a thread to handle it.
     */
    inbound = calloc (1, sizeof *inbound);
    inbound->next   = inbound;
    inbound->confd  = confd;
    inbound->screen = screen;
    rc = pthread_create (&inbound_thread, NULL, connection_thread, inbound);
    if (rc != 0) {
        fprintf (stderr, "kkscreen: pthread_create() error: %s\n", strerror (rc));
        return 2;
    }
    return 0;
}


/**
 * @brief Take screen data generated by user process and copy to screen ring buffer
 *        and also to any currently connected streams.
 */
static int handle_screen (Screen *screen)
{
    char buf[4096];
    Inbound *inbound;
    int rc;

    /*
     * Wait for some screen data from user process or for user process to exit.
     */
    while ((rc = read (screen->ptyfd, buf, sizeof buf)) > 0) {

        /*
         * Stuff the data in the ring buffer in case someone connects a little later.
         */
        pthread_mutex_lock (&screen->mutex);
        int ins = screen->insert;
        if (ins + rc < sizeof screen->buf) {
            memcpy (screen->buf + ins, buf, rc);
            screen->insert = ins + rc;
        } else {
            memcpy (screen->buf + ins, buf, sizeof screen->buf - ins);
            memcpy (screen->buf, buf + sizeof screen->buf - ins, ins + rc - sizeof screen->buf);
            screen->insert  = ins + rc - sizeof screen->buf;
            screen->wrapped = TRUE;
        }

        /*
         * And send the data out to anyone currently connected.
         */
        for (inbound = screen->inbounds; inbound != NULL; inbound = inbound->next) {
            if (!inbound->writebad && !writepipe (inbound->confd, buf, rc)) {
                fprintf (stderr, "kkscreen: write() pipe error: %s\n", strerror (errno));
                inbound->writebad = TRUE;
            }
        }
        pthread_mutex_unlock (&screen->mutex);
    }

    /*
     * User process has exited.
     * EIO seems to be the normal exit code.
     */
    if ((rc < 0) && (errno != EIO)) {
        fprintf (stderr, "kkscreen: read() pty error: %s\n", strerror (errno));
        rc = 2;
    }

    /*
     * Send EOF marker across to all inbound connections.
     * They should disconnect and that will shut down the connection_thread() threads.
     */
    pthread_mutex_lock (&screen->mutex);
    for (inbound = screen->inbounds; inbound != NULL; inbound = inbound->next) {
        writepipe (inbound->confd, endmsg, strlen (endmsg));
        shutdown (inbound->confd, SHUT_WR);
    }
    pthread_mutex_unlock (&screen->mutex);

    /*
     * All done.
     */
    return rc;
}


/**
 * @brief Take keyboard data from an inbound link and send it to user process.
 */
static void *connection_thread (void *inboundv)
{
    char buf[4096];
    Inbound *inbound, **linbound, *xinbound;
    Screen *screen;
    int end, len, ofs, rc;

    inbound = inboundv;
    screen = inbound->screen;

    // so we don't need to pthread_join() this thread
    pthread_detach (pthread_self ());

    /*
     * But before we connect it up for userprocess->link copy,
     * copy out anything that's in the screen ring buffer.
     */
    pthread_mutex_lock (&screen->mutex);
    if ((screen->wrapped && !writepipe (inbound->confd, screen->buf + screen->insert, sizeof screen->buf - screen->insert)) ||
                            !writepipe (inbound->confd, screen->buf, screen->insert)) {
        fprintf (stderr, "kkscreen: write() pipe error: %s\n", strerror (errno));
        rc = 2;
        goto done2;
    }

    /*
     * Now it's OK for handle_screen() to write screen data to this link.
     */
    inbound->next = screen->inbounds;
    screen->inbounds = inbound;

    /*
     * Maybe user process is blocked until first attach completes.
     */
    if (screen->waitfds[1] >= 0) {
        close (screen->waitfds[1]);
        screen->waitfds[1] = -1;
    }

    pthread_mutex_unlock (&screen->mutex);

    /*
     * Wait for some keyboard data from the link or for link to close.
     */
    while ((rc = read (inbound->confd, buf, sizeof buf - 128)) > 0) {
        for (ofs = 0; ofs < rc; ofs = end) {
            len = (int)(signed char)(buf[ofs]);

            /*
             * First byte < 0: command string.
             */
            if (len < 0) {
                end = ofs - len + 1;
                if ((end > rc) && !readpipe (inbound->confd, buf + rc, end - rc)) {
                    fprintf (stderr, "kkscreen: read() pty error: %s\n", strerror (errno));
                    rc = 2;
                    goto done1;
                }
                incoming_command (inbound, &buf[ofs+1], -len);
            }

            /*
             * Otherwise, data string.
             */
            else {
                end = ofs + len + 2;
                if ((end > rc) && !readpipe (inbound->confd, buf + rc, end - rc)) {
                    fprintf (stderr, "kkscreen: read() pty error: %s\n", strerror (errno));
                    rc = 2;
                    goto done1;
                }
                if (!writepipe (screen->ptyfd, &buf[ofs+1], len + 1)) {
                    fprintf (stderr, "kkscreen: write() pty error: %s\n", strerror (errno));
                    rc = 2;
                    goto done1;
                }
            }
        }
    }
    if (rc < 0) {
        fprintf (stderr, "kkscreen: read() pipe error: %s\n", strerror (errno));
        rc = 2;
    }

done1:
    pthread_mutex_lock (&screen->mutex);
    for (linbound = &screen->inbounds; (xinbound = *linbound) != inbound; linbound = &xinbound->next) { }
    *linbound = inbound->next;
done2:
    pthread_mutex_unlock (&screen->mutex);
    close (inbound->confd);
    free (inbound);
    return (void *)(long)rc;
}

static void incoming_command (Inbound *inbound, char *buf, int len)
{
    char cmd[len+1], *p;
    Screen *screen;
    struct winsize winsz;

    memcpy (cmd, buf, len);
    cmd[len] = 0;
    screen = inbound->screen;

    if (strcmp (cmd, "die") == 0) {
        fprintf (stderr, "kkscreen: die received\n");
        unlink (crsockaddr.sun_path);
        exit (-1);
    }
    if (memcmp (cmd, "ws:", 3) == 0) {
        memset (&winsz, 0, sizeof winsz);
        winsz.ws_col = strtoul (cmd + 3, &p, 0);
        if (*p == ':') {
            winsz.ws_row = strtoul (++ p, &p, 0);
            if (*p == 0) {
                inbound->lastwidth  = winsz.ws_col;
                inbound->lastheight = winsz.ws_row;
                pthread_mutex_lock (&screen->mutex);
                for (inbound = screen->inbounds; inbound != NULL; inbound = inbound->next) {
                    if (winsz.ws_col > inbound->lastwidth)  winsz.ws_col = inbound->lastwidth;
                    if (winsz.ws_row > inbound->lastheight) winsz.ws_row = inbound->lastheight;
                }
                if (ioctl (screen->ptyfd, TIOCSWINSZ, &winsz) < 0) {
                    fprintf (stderr, "kkscreen: ioctl(TIOCSWINSZ) error: %s\n", strerror (errno));
                }
                screen->curwidth  = winsz.ws_col;
                screen->curheight = winsz.ws_row;
                pthread_mutex_unlock (&screen->mutex);
                return;
            }
        }
        fprintf (stderr, "kkscreen: bad window size command: %s\n", cmd);
        return;
    }

    fprintf (stderr, "kkscreen: unknown command: %s\n", cmd);
}

/******************************\
 *  inject <sessionname> ...  *
\******************************/

static int cmd_inject (int argc, char **argv)
{
    char ccbuf[129], *name, *p;
    int i, rc, sockfd;

    if ((argc < 2) || (argv[1][0] == '-')) {
        fprintf (stderr, "kkscreen: missing <sessionname>\n");
        goto usage;
    }
    name = argv[1];

    /*
     * Open connection to server.
     */
    sockfd = outbound_connect (name);
    if (sockfd < 0) {
        if (sockfd != -999999999) fprintf (stderr, "kkscreen: connect(%s) error: %s\n", name, strerror (-sockfd));
        rc = 2;
        goto done;
    }

    /*
     * Send whatever we were given on the command line.
     * Flush any incoming data beforehand to keep link open.
     */
    for (i = 1; ++ i < argc;) {
        if (strcmp (argv[i], "-charcode") == 0) {
            if (++ i >= argc) {
                fprintf (stderr, "kkscreen: -charcode missing arg\n");
                rc = 1;
                goto done;
            }
            ccbuf[0] = 0;
            ccbuf[1] = strtol (argv[i], &p, 0);
            if (*p != 0) {
                fprintf (stderr, "kkscreen: bad char code %s\n", argv[i]);
                rc = 1;
                goto done;
            }
            flushpipereads (sockfd);
            if (!writepipe (sockfd, ccbuf, 2)) {
                fprintf (stderr, "kkscreen: write() pipe error: %s\n", strerror (errno));
                rc = 2;
                goto done;
            }
        }
        if (strcmp (argv[i], "-string") == 0) {
            if (++ i >= argc) {
                fprintf (stderr, "kkscreen: -string missing arg\n");
                rc = 1;
                goto done;
            }
            for (p = argv[i]; *p != 0; p += rc) {
                rc = strlen (p);
                if (rc > 128) rc = 128;
                ccbuf[0] = rc - 1;
                memcpy (ccbuf + 1, p, rc);
                flushpipereads (sockfd);
                if (!writepipe (sockfd, ccbuf, rc + 1)) {
                    fprintf (stderr, "kkscreen: write() pipe error: %s\n", strerror (errno));
                    rc = 2;
                    goto done;
                }
            }
        }
    }

    /*
     * Send EOF mark to server so it will disconnect link after processing whatever we sent.
     */
    flushpipereads (sockfd);
    if (shutdown (sockfd, SHUT_WR) < 0) {
        fprintf (stderr, "kkscreen: shutdown() pipe error: %s\n", strerror (errno));
        rc = 2;
        goto done;
    }

    /*
     * Wait for server to see the EOF mark and close link to be sure it sees everything we sent.
     * Otherwise it might drop link if it gets an EPIPE error from a write before it processes
     * something we sent.
     */
    flushpipereads (sockfd);
    while (read (sockfd, ccbuf, sizeof ccbuf) > 0) { }

    rc = 0;

done:
    close (sockfd);
    return rc;

usage:
    fprintf (stderr, "usage: kkscreen inject <sessionname> { [ -charcode <charcode> ] [ -string <string> ] }\n");
    return 1;
}

static void flushpipereads (int fd)
{
    char buf[4096];
    fd_set readmask;
    int rc;
    struct timeval timeout;

    while (TRUE) {
        FD_ZERO (&readmask);
        FD_SET (fd, &readmask);
        memset (&timeout, 0, sizeof timeout);
        do rc = select (fd + 1, &readmask, NULL, NULL, &timeout);
        while ((rc < 0) && (errno == EINTR));
        if (rc <= 0) break;
        unusedint (read (fd, buf, sizeof buf));
    }
}

static void unusedint (int rc)
{ }

/************************\
 *  kill <sessionname>  *
\************************/

static int cmd_kill (int argc, char **argv)
{
    char *name;

    if (argc < 2) {
        fprintf (stderr, "kkscreen: missing <sessionname>\n");
        goto usage;
    }
    if (argc > 2) {
        fprintf (stderr, "kkscreen: unknown argument/option %s\n", argv[2]);
        goto usage;
    }
    name = argv[1];

    do_kill (name);
    return 0;

usage:
    fprintf (stderr, "usage: kkscreen kill <sessionname>\n");
    return 1;
}


/**
 * @brief Tell existing server to die.
 */
static void do_kill (char const *name)
{
    char buf[256];
    int sockfd;

    sockfd = outbound_connect (name);
    if (sockfd >= 0) {
        if (!writepipe (sockfd, "\375die", 4)) {
            fprintf (stderr, "kkscreen: writepipe(kill) error: %s\n", strerror (errno));
        } else {
            while (read (sockfd, buf, sizeof buf) > 0) { }
        }
        close (sockfd);
    }
}

/***********************\
 *  list [<username>]  *
\***********************/

static int cmd_list (int argc, char **argv)
{
    char *p;
    int i, myuid;
    struct passwd *pwd;

    if (argc == 1) do_list (geteuid ());
    else {
        for (i = 0; ++ i < argc;) {
            myuid = strtol (argv[i], &p, 0);
            if (*p != 0) {
                pwd = getpwnam (argv[i]);
                if (pwd == NULL) {
                    fprintf (stderr, "kkscreen: bad uid/username %s\n", argv[i]);
                    return 2;
                }
                do_list (pwd->pw_uid);
            } else {
                do_list (myuid);
            }
        }
    }
    return 0;
}

static void do_list (int myuid)
{
    char buf[256], *name, *status, *uidstr;
    int i, nents, shown, sockfd;
    struct dirent **namelist;
    struct passwd *pwd;
    struct sockaddr_un sockaddr;
    struct stat statbuf;
    struct tm lcl;

    pwd = getpwuid (myuid);
    if (pwd == NULL) {
        uidstr = alloca (12);
        sprintf (uidstr, "%d", myuid);
    } else {
        uidstr = alloca (strlen (pwd->pw_name) + 1);
        strcpy (uidstr, pwd->pw_name);
    }

    sprintf (do_list_filter_param, "kkscreen.%d.", myuid);

    nents = scandir ("/tmp", &namelist, do_list_filter, alphasort);
    if (nents < 0) {
        fprintf (stderr, "kkscreen: scandir(/tmp) error: %s\n", strerror (errno));
        return;
    }

    shown = FALSE;
    for (i = 0; i < nents; i ++) {
        name = namelist[i]->d_name;

        memset (&sockaddr, 0, sizeof sockaddr);
        sockaddr.sun_family = AF_UNIX;
        if (strlen (name) + 6 < sizeof sockaddr.sun_path) {
            snprintf (sockaddr.sun_path, sizeof sockaddr.sun_path, "/tmp/%s", name);

            if (stat (sockaddr.sun_path, &statbuf) >= 0) {
                status = "dead";
                sockfd = socket (AF_UNIX, SOCK_STREAM, 0);
                if (sockfd >= 0) {
                    if (connect (sockfd, (void *)&sockaddr, sizeof sockaddr) >= 0) {
                        shutdown (sockfd, SHUT_WR);
                        while (read (sockfd, buf, sizeof buf) > 0) { }
                        status = "live";
                    }
                    close (sockfd);
                }

                lcl = *localtime (&statbuf.st_mtime);
                printf ("  %04d-%02d-%02d %02d:%02d:%02d  %s  %s/%s\n", 
                        lcl.tm_year + 1900, lcl.tm_mon + 1, lcl.tm_mday,
                        lcl.tm_hour, lcl.tm_min, lcl.tm_sec,
                        status, uidstr, name + strlen (do_list_filter_param));
                shown = TRUE;
            }
        }
        free (namelist[i]);
    }
    free (namelist);

    if (!shown) {
        fprintf (stderr, "kkscreen: no entries for %s\n", uidstr);
    }
}

static int do_list_filter (struct dirent const *de)
{
    int len = strlen (do_list_filter_param);
    return memcmp (de->d_name, do_list_filter_param, len) == 0;
}

/**
 * @brief Try to connect to server.
 */
static int outbound_connect (char const *name)
{
    int err, sockfd;
    struct sockaddr_un sockaddr;

    sockfd = socket (AF_UNIX, SOCK_STREAM, 0);
    if (sockfd < 0) return -errno;

    err = get_sock_name (&sockaddr, name);
    if (err < 0) return -999999999;

    if (connect (sockfd, (void *)&sockaddr, sizeof sockaddr) < 0) {
        err = errno;
        close (sockfd);
        return -err;
    }
    return sockfd;
}


/**
 * @brief Fill in sockaddr with the name of the unix socket.
 *        Return UID used.
 */
static int get_sock_name (struct sockaddr_un *sa, char const *name)
{
    char const *p;
    char *q;
    int myuid, rc;
    struct passwd *pwd;

    /*
     * Decode uid/username prefix on name, if any.
     *    <simplename> = use caller's euid
     *    <uid>/<simplename> = use the given uid
     *    <username>/<simplename> = use the given user's uid
     */
    myuid = geteuid ();
    p = strchr (name, '/');
    if (p != NULL) {
        myuid = strtol (name, &q, 0);
        if (q != p) {
            char un[p-name+1];
            memcpy (un, name, p - name);
            un[p-name] = 0;
            pwd = getpwnam (un);
            if (pwd == NULL) {
                fprintf (stderr, "kkscreen: unknown username %s on name %s\n", un, name);
                return -1;
            }
            myuid = pwd->pw_uid;
        } else {
            pwd = getpwuid (myuid);
            if (pwd == NULL) {
                fprintf (stderr, "kkscreen: unknown uid %d on name %s\n", myuid, name);
                return -1;
            }
        }
        if (strchr (++ p, '/') != NULL) {
            fprintf (stderr, "kkscreen: name cannot have two slashes %s\n", name);
            return -1;
        }
        name = p;
    }

    /*
     * Fill in sockaddr_un struct.
     */
    memset (sa, 0, sizeof *sa);
    sa->sun_family = AF_UNIX;
    rc = snprintf (sa->sun_path, sizeof sa->sun_path, "/tmp/kkscreen.%d.%s", myuid, name);
    if (rc >= sizeof sa->sun_path) {
        fprintf (stderr, "kkscreen: name %s too long\n", name);
        return -1;
    }

    /*
     * Let caller know the UID that we used.
     */
    return myuid;
}

/**
 * @brief Read whole buffer from the pipe.
 * @returns FALSE: failed (see errno)
 *           TRUE: successful
 */
static int readpipe (int fd, char *buf, int len)
{
    int rc;

    while (len > 0) {
        rc = read (fd, buf, len);
        if (rc <= 0) {
            if (rc == 0) errno = EPIPE;
            return FALSE;
        }
        buf += rc;
        len -= rc;
    }
    return TRUE;
}

/**
 * @brief Write whole buffer to the pipe.
 * @returns FALSE: failed (see errno)
 *           TRUE: successful
 */
static int writepipe (int fd, char const *buf, int len)
{
    int rc;

    while (len > 0) {
        rc = write (fd, buf, len);
        if (rc <= 0) {
            if (rc == 0) errno = EPIPE;
            return FALSE;
        }
        buf += rc;
        len -= rc;
    }
    return TRUE;
}
