from subprocess import check_output, CalledProcessError


def output_of(command, stderr=None):
    """

    :param command:
    :return:
    """
    try:
        return check_output(command, shell=True, stderr=stderr).decode("UTF-8")
    except CalledProcessError as exc:
        return exc.output.decode("UTF-8")
