# Decomment the following lines to build the Docker image for different architectures
# For arm64 architecture
# FROM maven:3.8.7-openjdk-18-slim@sha256:4757c1ff47a6139f6a7e6a3ef4c2bef630422b74a636d46f56ea5f16b966076a

# For x86_64 architecture
FROM maven:3.8.7-openjdk-18-slim@sha256:6e08ab80ed557294e30c9555c923e7620a8125b4f207996d961535789088339b

RUN apt-get update && \
    apt-get install -y \
    graphviz \
    curl \
    git \
    virtualenv \
    python3 \
    python3-pip \
    nano \
    && apt-get clean && rm -rf /var/lib/apt/lists/*

WORKDIR /replication-pkg

COPY examples/ examples
COPY Alloy4PA/ Alloy4PA
COPY config.properties .
COPY README.md .
COPY table_1.py .

RUN mvn install:install-file  -Dfile="Alloy4PA/libs/org.alloytools.alloy6.dist.jar"  -DgroupId="org.alloytools.alloy6.dist"  -DartifactId="alloy"  -Dversion="6.0.0"  -Dpackaging="jar"

RUN cd Alloy4PA && mvn clean package

RUN cd ..

CMD ["sh"]