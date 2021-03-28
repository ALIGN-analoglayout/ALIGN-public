This directory contains setup specifications for a Native flow and a container-based flow that runs the
end-to-end ALIGN flow using Makefile. For container-based flow in addition to Docker,
you will need to install docker-compose which is used to have  individual
engines for isolated software environments.

Software components that are in container images can be thought of as
'installed' and we are using Make to run the flow through the
components.

## Makefile usage

You can use the Makefile to either run the ALIGN flow through a native Linux build of
all the components in the current environment (assuming you have all
software prerequisites installed) or you can invoke the container-based flow using
either a Docker volume for data input/output (you can mount a local directory into Docker container).

You will need to set two environment variables to run the Makefile in
any environment. First is the ALIGN\_HOME variable which should point
the top directory of the ALIGN analog system.

		% export ALIGN_HOME=<top of ALIGN source area>

Second is a working directory ALIGN\_WORK\_DIR, which can either be
the full path to a working directory or a docker volume name.

		% export ALIGN_WORK_DIR=<your Linux working area>


## Native Environment Flow

To invoke a native Linux environment flow Makefile can be used to issue native
Linux build commands.  While using a native environment 
all software requirements must be built into the native environment,
including handling any version conflicts, and when a new component is
needed, it and its environment need to be integrated before any
testing can start. The Makefile expects the Python environment in the directory "/opt/venv"
 which can be modified to python virtual environment path.

Here are the sequence of commands needed to invoke make in a native
environment.
	
		% export ALIGN_WORK_DIR=<your Linux working area>
		% cd $ALIGN_WORK_DIR
		% ln -s $ALIGN_HOME/build/Makefile .
		% make DESIGN=<design>

## Docker based flow
To setup using a Docker volume in a container-based flow:

		% docker volume create <volumeName>
		% export ALIGN_WORK_DIR=<volumeName>
To setup using a working directory in a container-based flow (In WSL,
this directory must be the full path to a Windows shared directory):


		% export ALIGN_WORK_DIR=<working directory path for output>

Now invoke the flow:

		% cd $ALIGN_HOME/build
		% make docker DESIGN=<design>

To rebuild an image (analogous to reinstalling a component), you can
use docker-compose to update the container:

		% cd $ALIGN_HOME/build
		% docker-compose up -d --build <service-name>

You can work inside the container to modify or debug its behavior:

		% cd $ALIGN_HOME/build
		% docker-compose exec <service-name> bash
		 $ <start your commands here>
		 $
		
> Here, docker-compose will first bring up a make-docker-service which
> contains the main Makefile and docker-compose configuration.  Then
> it will bring up the rest of the services from within the
> make-docker-service.  After that, make will run the flow for the
> given design.

If the services don't all come up, you can bring down the services (removing the containers)
to retry:

		% make docker-down

If you change source and start with a fresh set of images from which
containers are built, you can either bring them down then up
individually using the docker-compose commands (see end of this page)
or flush all images and restart:

		% make docker-fulldown
		
		
### A Monolithic Docker Container for the ALIGN flow
We have provided a Dockerfile in build/Dockerfile.native that builds
up a monolithic Linux environment to help test the functionality of
operating in a native environment.It is hard to keep it centrally up
to date, so as components add more dependencies, this file may be out
of date.  But it serves as a starting point for the full environment.
The container can be built as a service called fullbuild-service.  You
can then run the above commands in the container as if it were your
native environment as shown below:
	
		% cd $ALIGN_HOME/build
		% docker-compose up -d fullbuild-service
		% docker-compose exec fullbuild-service bash
		 $ cd <a_work_area_inside_container>
		 $ ln -s $ALIGN_HOME/build/Makefile .
		 $ make DESIGN=<design>
		
## Useful docker-compose commands

You must be in the directory where the service configuration file
(usually docker-compose.yml) resides.  If the directory name does not
match, then the services can only be found by using the -p <project>
where project is the original directory name or project name used to
bring up the services.

- docker-compose up -d:  bring up all services (build images if needed)
  
- docker-compose down:  shut down all services and remove containers
  - --rmi all: remove images too
  
- docker-compose up -d <service>:  bring up a specific service.  This will set any environment variables and bind volumes at the time of bring-up (even if already up).
  
- docker-compose up -d --build <service>:  build and bring up a service
  
- docker-compose exec <service> <command>:  execute a command on a running container

Note that services that are 'up' are live and have live filesystems.
Edits there will impact the overall flow, so you can check changes by
modifying files inside the relevant containers.  You can git push from
those containers as well.
