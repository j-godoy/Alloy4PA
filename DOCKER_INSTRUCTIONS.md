# Docker Usage Instructions

This guide explains how to build and run the Docker container for the Alloy4PA artifact.

## 2. Build the Docker image

> Note: the Dockerfile is set up to work with both x86_64 and ARM architectures. You can uncomment the appropriate `FROM` line in the Dockerfile depending on your architecture. Default is set for x86_64. If you are using an ARM architecture, uncomment the line 3 and comment the line 6.

Run the following command in the directory containing the Dockerfile:

```sh
docker build -t alloy4pa-replication .
```

- `-t alloy4pa-replication` names the image (you can choose another name).
- The `.` means "build using the current directory".

- This will copy the necessary files and compile the Java project, generating the corresponding .jar file.

## 3. Run the Docker container

To start an interactive shell inside the container:

```sh
docker run -it alloy4pa-replication
```

This will open a shell (`sh`) in the `/replication-pkg` directory inside the container.

## 4. Run an experiment inside the container

For example, to run the tool on a sample model:

```sh
java -jar Alloy4PA/target/Alloy4PA-1.0.0-fat-jar-with-dependencies.jar examples/Benchmarks/B1/alloy_models/BasicProvenance.als
```

---
