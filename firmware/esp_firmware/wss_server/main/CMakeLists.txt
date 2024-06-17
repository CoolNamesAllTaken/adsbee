idf_component_register(SRCS "adsbee_server.cc" "keep_alive.c"
                    INCLUDE_DIRS "."
                    EMBED_TXTFILES "certs/servercert.pem"
                                   "certs/prvtkey.pem")
